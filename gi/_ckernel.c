/* gi/_ckernel.c: optional compiled kernel for the hottest primitives of gi/.
 *
 * Build with `python3 build_ckernel.py` (see README.md and docs/w16-ckernel.md);
 * gi/kernel.py loads the result, and GI_NO_CKERNEL=1 disables it.
 *
 * Contract. Every function computes exactly what its Python reference computes
 * (gi/perm.py, gi/group.py, gi/refine.py, which stay the definition):
 *
 *   - the fast path handles only the input shape the solver produces (exact
 *     tuples or lists of exact ints in range);
 *   - any other input is not an error here. perm.* call the registered Python
 *     reference, the others return None and the Python caller runs its own
 *     body, so invalid input gets the reference's result or exception. No
 *     state is changed before that decision.
 *
 * Integer arithmetic in wl2_single is modulo 2^128 or 2^64. The reference
 * computes exact integers whose final values are below those bounds (the
 * table bit sizes of refine._tables guarantee it), so the results are equal.
 */
#define PY_SSIZE_T_CLEAN
#include <Python.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define CK_API_VERSION 1
#ifndef CK_SOURCE_HASH
#define CK_SOURCE_HASH ""
#endif

#if PY_VERSION_HEX >= 0x030C0000
#define CK_IS_COMPACT(o) PyUnstable_Long_IsCompact((const PyLongObject *)(o))
#define CK_COMPACT(o) PyUnstable_Long_CompactValue((const PyLongObject *)(o))
#else
static inline int ck_fits(PyObject *o, Py_ssize_t *v)
{
    int ov = 0;
    long long x = PyLong_AsLongLongAndOverflow(o, &ov);
    if (ov || x > 1073741823LL || x < -1073741823LL) { PyErr_Clear(); return 0; }
    *v = (Py_ssize_t)x;
    return 1;
}
#endif

/* The value of an exact int below 2^30 in absolute value; 0 for anything else. */
static inline int read_small(PyObject *o, Py_ssize_t *out)
{
    if (!PyLong_CheckExact(o))
        return 0;
#if PY_VERSION_HEX >= 0x030C0000
    if (!CK_IS_COMPACT(o))
        return 0;
    *out = CK_COMPACT(o);
    return 1;
#else
    return ck_fits(o, out);
#endif
}

/* An index in [0, m); 0 for anything else. */
static inline int read_index(PyObject *o, Py_ssize_t m, Py_ssize_t *out)
{
    Py_ssize_t v;
    if (!read_small(o, &v) || v < 0 || v >= m)
        return 0;
    *out = v;
    return 1;
}

/* -- shared int objects -------------------------------------------------- */
/* Boxing is the largest cost of returning permutations, so the ints 0..cap-1
 * are made once. Only degrees up to CK_INTS_MAX use the table. Nothing keeps
 * a pointer into ints_tab across a call that can run Python code. */
#define CK_INTS_MAX ((Py_ssize_t)1 << 22)
static PyObject **ints_tab = NULL;
static Py_ssize_t ints_cap = 0;

/* 1 if ints below n are available, 0 if n is too large, -1 with an exception. */
static int ints_ensure(Py_ssize_t n)
{
    Py_ssize_t cap, i;
    PyObject **t;
    if (n <= ints_cap)
        return 1;
    if (n > CK_INTS_MAX)
        return 0;
    cap = ints_cap ? ints_cap : 1024;
    while (cap < n)
        cap *= 2;
    if (cap > CK_INTS_MAX)
        cap = CK_INTS_MAX;
    t = PyMem_Realloc(ints_tab, (size_t)cap * sizeof(PyObject *));
    if (t == NULL) {
        PyErr_NoMemory();
        return -1;
    }
    ints_tab = t;
    for (i = ints_cap; i < cap; i++) {
        PyObject *v = PyLong_FromSsize_t(i);
        if (v == NULL)
            return -1;                  /* ints_cap still counts the valid ones */
        ints_tab[i] = v;
        ints_cap = i + 1;
    }
    return 1;
}

static inline PyObject *int_ref(Py_ssize_t v)     /* a new reference; v < ints_cap */
{
    PyObject *o = ints_tab[v];
    Py_INCREF(o);
    return o;
}

/* -- fallbacks to the Python references ----------------------------------- */
static PyObject *fb_mul, *fb_inv, *fb_act, *fb_maps;

static PyObject *call_fb(PyObject *fb, PyObject *const *args, Py_ssize_t nargs)
{
    if (fb == NULL) {
        PyErr_SetString(PyExc_RuntimeError, "_ckernel: fallbacks are not registered");
        return NULL;
    }
    return PyObject_Vectorcall(fb, args, (size_t)nargs, NULL);
}

static PyObject *ck_set_fallbacks(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    Py_ssize_t i;
    PyObject **slots[4] = {&fb_mul, &fb_inv, &fb_act, &fb_maps};
    (void)m;
    if (nargs != 4) {
        PyErr_SetString(PyExc_TypeError, "set_fallbacks(mul, inv, act, maps)");
        return NULL;
    }
    for (i = 0; i < 4; i++) {
        Py_INCREF(args[i]);
        Py_XSETREF(*slots[i], args[i]);
    }
    Py_RETURN_NONE;
}

/* -- permutations (gi/perm.py) -------------------------------------------- */
static PyObject *ck_mul(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *p, *q, *res;
    Py_ssize_t n, d, i, v;
    (void)m;
    if (nargs != 2 || !PyTuple_CheckExact(args[0]) || !PyTuple_CheckExact(args[1]))
        return call_fb(fb_mul, args, nargs);
    p = args[0];
    q = args[1];
    n = PyTuple_GET_SIZE(p);
    d = PyTuple_GET_SIZE(q);
    res = PyTuple_New(n);
    if (res == NULL)
        return NULL;
    for (i = 0; i < n; i++) {
        PyObject *o;
        if (!read_index(PyTuple_GET_ITEM(p, i), d, &v)) {
            Py_DECREF(res);
            return call_fb(fb_mul, args, nargs);
        }
        o = PyTuple_GET_ITEM(q, v);
        Py_INCREF(o);
        PyTuple_SET_ITEM(res, i, o);
    }
    return res;
}

static PyObject *ck_inv(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *p, *res;
    Py_ssize_t n, i, v;
    int32_t sbuf[512], *r = sbuf;
    int ok;
    (void)m;
    if (nargs != 1 || !PyTuple_CheckExact(args[0]))
        return call_fb(fb_inv, args, nargs);
    p = args[0];
    n = PyTuple_GET_SIZE(p);
    ok = ints_ensure(n);
    if (ok < 0)
        return NULL;
    if (ok == 0 || n > INT32_MAX)
        return call_fb(fb_inv, args, nargs);
    if (n > 512) {
        r = malloc((size_t)n * sizeof(int32_t));
        if (r == NULL)
            return PyErr_NoMemory();
    }
    /* A repeated image overwrites and a missed slot stays 0, as in the reference. */
    memset(r, 0, (size_t)n * sizeof(int32_t));
    for (i = 0; i < n; i++) {
        if (!read_index(PyTuple_GET_ITEM(p, i), n, &v)) {
            if (r != sbuf)
                free(r);
            return call_fb(fb_inv, args, nargs);
        }
        r[v] = (int32_t)i;
    }
    res = PyTuple_New(n);
    if (res != NULL)
        for (i = 0; i < n; i++)
            PyTuple_SET_ITEM(res, i, int_ref(r[i]));
    if (r != sbuf)
        free(r);
    return res;
}

static PyObject *ck_act(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *x, *g, *res;
    PyObject **items;
    Py_ssize_t n, i, v;
    (void)m;
    if (nargs != 2 || !(PyTuple_CheckExact(args[0]) || PyList_CheckExact(args[0]))
        || !PyTuple_CheckExact(args[1]))
        return call_fb(fb_act, args, nargs);
    x = args[0];
    g = args[1];
    n = PySequence_Fast_GET_SIZE(x);
    if (PyTuple_GET_SIZE(g) < n)
        return call_fb(fb_act, args, nargs);
    res = PyTuple_New(n);
    if (res == NULL)
        return NULL;
    items = PySequence_Fast_ITEMS(x);   /* no Python code runs before the last use */
    for (i = 0; i < n; i++) {
        PyObject *c = items[i], *old;
        if (!read_index(PyTuple_GET_ITEM(g, i), n, &v)) {
            Py_DECREF(res);
            return call_fb(fb_act, args, nargs);
        }
        old = PyTuple_GET_ITEM(res, v);
        Py_INCREF(c);
        PyTuple_SET_ITEM(res, v, c);
        Py_XDECREF(old);                /* (a repeated image overwrites) */
    }
    for (i = 0; i < n; i++)             /* (a missed slot stays None) */
        if (PyTuple_GET_ITEM(res, i) == NULL) {
            Py_INCREF(Py_None);
            PyTuple_SET_ITEM(res, i, Py_None);
        }
    return res;
}

static PyObject *ck_maps(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *g, *x, *y;
    Py_ssize_t n, d, i, v, a, b;
    (void)m;
    if (nargs != 3 || !PyTuple_CheckExact(args[0]) || !PyTuple_CheckExact(args[1])
        || !PyTuple_CheckExact(args[2]))
        return call_fb(fb_maps, args, nargs);
    g = args[0];
    x = args[1];
    y = args[2];
    n = PyTuple_GET_SIZE(x);
    d = PyTuple_GET_SIZE(y);
    if (PyTuple_GET_SIZE(g) != n)
        return call_fb(fb_maps, args, nargs);
    for (i = 0; i < n; i++) {
        if (!read_index(PyTuple_GET_ITEM(g, i), d, &v)
            || !read_small(PyTuple_GET_ITEM(x, i), &a)
            || !read_small(PyTuple_GET_ITEM(y, v), &b))
            return call_fb(fb_maps, args, nargs);
        if (a != b) {
            /* The reference checks only the first 4 points before a full pass.
             * Beyond them it reads all of g first, so a bad entry later in g
             * raises there. Let it decide unless g is valid to the end. */
            Py_ssize_t j;
            if (n > 4 && i >= 4)
                for (j = i + 1; j < n; j++) {
                    Py_ssize_t w;
                    if (!read_index(PyTuple_GET_ITEM(g, j), d, &w))
                        return call_fb(fb_maps, args, nargs);
                }
            Py_RETURN_FALSE;
        }
    }
    Py_RETURN_TRUE;
}

/* -- orbits (PermGroup.orbits) -------------------------------------------- */
/* orbits(n, gens): the orbits as sorted lists, ordered by least point; None
 * if the input is not n and a list of exact tuples of ints in range(n). */
static PyObject *ck_orbits(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *gens, *res = NULL;
    Py_ssize_t n, ng, i, j, v, norb = 0;
    int32_t *flat = NULL, *label = NULL, *queue = NULL, *size = NULL, *fill = NULL;
    int ok;
    (void)m;
    if (nargs != 2 || !read_small(args[0], &n) || n < 0 || !PyList_CheckExact(args[1]))
        Py_RETURN_NONE;
    gens = args[1];
    ng = PyList_GET_SIZE(gens);
    ok = ints_ensure(n);
    if (ok < 0)
        return NULL;
    if (ok == 0)
        Py_RETURN_NONE;
    if (n == 0)
        return PyList_New(0);
    if (ng > 0 && (size_t)ng > SIZE_MAX / sizeof(int32_t) / (size_t)n)
        Py_RETURN_NONE;
    flat = malloc((size_t)(ng ? ng * n : 1) * sizeof(int32_t));
    label = malloc((size_t)n * sizeof(int32_t));
    queue = malloc((size_t)n * sizeof(int32_t));
    size = calloc((size_t)n, sizeof(int32_t));
    fill = calloc((size_t)n, sizeof(int32_t));
    if (!flat || !label || !queue || !size || !fill) {
        PyErr_NoMemory();
        goto done;
    }
    for (j = 0; j < ng; j++) {
        PyObject *g = PyList_GET_ITEM(gens, j);
        if (!PyTuple_CheckExact(g) || PyTuple_GET_SIZE(g) != n) {
            res = Py_None;
            Py_INCREF(res);
            goto done;
        }
        for (i = 0; i < n; i++) {
            if (!read_index(PyTuple_GET_ITEM(g, i), n, &v)) {
                res = Py_None;
                Py_INCREF(res);
                goto done;
            }
            flat[j * n + i] = (int32_t)v;
        }
    }
    memset(label, 0xff, (size_t)n * sizeof(int32_t));
    for (i = 0; i < n; i++) {
        Py_ssize_t head = 0, tail = 1;
        if (label[i] >= 0)
            continue;
        label[i] = (int32_t)norb;
        queue[0] = (int32_t)i;
        while (head < tail) {
            int32_t a = queue[head++];
            for (j = 0; j < ng; j++) {
                int32_t b = flat[j * n + a];
                if (label[b] < 0) {
                    label[b] = (int32_t)norb;
                    queue[tail++] = b;
                }
            }
        }
        size[norb] = (int32_t)tail;
        norb++;
    }
    res = PyList_New(norb);
    if (res == NULL)
        goto done;
    for (i = 0; i < norb; i++) {
        PyObject *o = PyList_New(size[i]);
        if (o == NULL) {
            Py_CLEAR(res);
            goto done;
        }
        PyList_SET_ITEM(res, i, o);
    }
    for (i = 0; i < n; i++) {           /* points increasing: each orbit is sorted */
        int32_t l = label[i];
        PyList_SET_ITEM(PyList_GET_ITEM(res, l), fill[l]++, int_ref(i));
    }
done:
    free(flat);
    free(label);
    free(queue);
    free(size);
    free(fill);
    return res;
}

/* -- sifting (PermGroup.sift, _sifts_to_id, _make_fast_plan) -------------- */
static PyObject *str_get;

/* A new reference to Ti[p]; NULL without an exception if p is absent, NULL with
 * one on error. Ti is a dict or a LazyTransversal (whose get may run Python). */
static PyObject *ti_lookup(PyObject *Ti, Py_ssize_t p)
{
    PyObject *key = int_ref(p), *t;
    if (PyDict_CheckExact(Ti)) {
        t = PyDict_GetItemWithError(Ti, key);
        Py_XINCREF(t);
    } else {
        t = PyObject_CallMethodOneArg(Ti, str_get, key);
        if (t == Py_None)
            Py_CLEAR(t);
    }
    Py_DECREF(key);
    return t;
}

/* g[i] = t[g[i]] for i < len, for a tuple t of ints; 0 if t is not as expected. */
static inline int apply_tuple(int32_t *g, Py_ssize_t len, PyObject *t, Py_ssize_t n)
{
    Py_ssize_t i, v;
    if (!PyTuple_CheckExact(t) || PyTuple_GET_SIZE(t) != n)
        return 0;
    for (i = 0; i < len; i++) {
        if (!read_index(PyTuple_GET_ITEM(t, g[i]), n, &v))
            return 0;
        g[i] = (int32_t)v;
    }
    return 1;
}

static PyObject *make_perm(const int32_t *g, Py_ssize_t n)
{
    Py_ssize_t i;
    PyObject *r = PyTuple_New(n);
    if (r != NULL)
        for (i = 0; i < n; i++)
            PyTuple_SET_ITEM(r, i, int_ref(g[i]));
    return r;
}

/* sift(g, plan, Tis, base) -> (residue, level), or None to use the reference.
 * plan is PermGroup._make_plan's list of (l, b, None, None) and (l, None, get,
 * fix). A step never changes anything visible, so None can be returned at any
 * point. */
static PyObject *ck_sift(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *g0, *plan, *Tis, *base, *res = NULL, *out = NULL;
    Py_ssize_t n, i, np, v, level = -1, nbase;
    int32_t sbuf[512], *g = sbuf;
    int changed = 0, ok, stop = 0;
    (void)m;
    if (nargs != 4 || !PyTuple_CheckExact(args[0]) || !PyList_CheckExact(args[1])
        || !PyList_CheckExact(args[2]) || !PyList_CheckExact(args[3]))
        Py_RETURN_NONE;
    g0 = args[0];
    plan = args[1];
    Tis = args[2];
    base = args[3];
    n = PyTuple_GET_SIZE(g0);
    nbase = PyList_GET_SIZE(base);
    ok = ints_ensure(n);
    if (ok < 0)
        return NULL;
    if (ok == 0)
        Py_RETURN_NONE;
    if (n > 512) {
        g = malloc((size_t)n * sizeof(int32_t));
        if (g == NULL)
            return PyErr_NoMemory();
    }
    for (i = 0; i < n; i++) {
        if (!read_index(PyTuple_GET_ITEM(g0, i), n, &v))
            goto use_python;
        g[i] = (int32_t)v;
    }
    np = PyList_GET_SIZE(plan);
    for (i = 0; i < np && !stop; i++) {
        PyObject *step = PyList_GET_ITEM(plan, i);
        Py_ssize_t l, b;
        if (!PyTuple_CheckExact(step) || PyTuple_GET_SIZE(step) != 4
            || !read_small(PyTuple_GET_ITEM(step, 0), &l) || l < 0)
            goto use_python;
        if (PyTuple_GET_ITEM(step, 2) == Py_None) {
            Py_ssize_t p;
            if (!read_index(PyTuple_GET_ITEM(step, 1), n, &b))
                goto use_python;
            p = g[b];
            if (p != b) {
                PyObject *Ti, *t;
                int done;
                if (l >= PyList_GET_SIZE(Tis))
                    goto use_python;
                Ti = PyList_GET_ITEM(Tis, l);
                t = ti_lookup(Ti, p);
                if (t == NULL) {
                    if (PyErr_Occurred())
                        goto done;
                    level = l;          /* no transversal element: stop here */
                    stop = 1;
                    break;
                }
                done = apply_tuple(g, n, t, n);
                Py_DECREF(t);
                if (!done)
                    goto use_python;
                changed = 1;
            }
        } else {                        /* a run of trivial levels */
            PyObject *fix = PyTuple_GET_ITEM(step, 3);
            Py_ssize_t j, nf, f;
            if (!PyTuple_CheckExact(fix))
                goto use_python;
            nf = PyTuple_GET_SIZE(fix);
            for (j = 0; j < nf; j++) {
                if (!read_index(PyTuple_GET_ITEM(fix, j), n, &f))
                    goto use_python;
                if (g[f] != f) {
                    /* The first level of the run whose point g moves. */
                    for (;;) {
                        if (l >= nbase
                            || !read_index(PyList_GET_ITEM(base, l), n, &b))
                            goto use_python;
                        if (g[b] == b)
                            l++;
                        else
                            break;
                    }
                    level = l;
                    stop = 1;
                    break;
                }
            }
        }
    }
    if (!stop)
        level = nbase;
    /* (with no multiplication the input object itself is the residue) */
    if (changed)
        out = make_perm(g, n);
    else {
        out = g0;
        Py_INCREF(out);
    }
    if (out == NULL)
        goto done;
    {
        PyObject *lv = PyLong_FromSsize_t(level);
        if (lv == NULL) {
            Py_DECREF(out);
            goto done;
        }
        res = PyTuple_New(2);
        if (res == NULL) {
            Py_DECREF(out);
            Py_DECREF(lv);
            goto done;
        }
        PyTuple_SET_ITEM(res, 0, out);
        PyTuple_SET_ITEM(res, 1, lv);
    }
    goto done;
use_python:
    res = Py_None;
    Py_INCREF(res);
done:
    if (g != sbuf)
        free(g);
    return res;
}

/* sifts_to_id(P, factors, steps, Tis): PermGroup._sifts_to_id after the plan
 * lookup; None to use the reference. */
static PyObject *ck_sifts_to_id(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *P, *factors, *steps, *Tis, *res = NULL;
    Py_ssize_t L, i, j, v, nf, ns, n = -1, maxp = 0;
    int32_t sbuf[512], *g = sbuf, *p0;
    int ok;
    (void)m;
    if (nargs != 4 || !PyTuple_CheckExact(args[0]) || !PyTuple_CheckExact(args[1])
        || !PyList_CheckExact(args[2]) || !PyList_CheckExact(args[3]))
        Py_RETURN_NONE;
    P = args[0];
    factors = args[1];
    steps = args[2];
    Tis = args[3];
    L = PyTuple_GET_SIZE(P);
    nf = PyTuple_GET_SIZE(factors);
    ns = PyList_GET_SIZE(steps);
    if (L == 0 || nf == 0)
        Py_RETURN_NONE;
    if (L > 256) {
        g = malloc(2 * (size_t)L * sizeof(int32_t));
        if (g == NULL)
            return PyErr_NoMemory();
    }
    p0 = g + L;
    for (i = 0; i < L; i++) {
        if (!read_small(PyTuple_GET_ITEM(P, i), &v) || v < 0)
            goto use_python;
        g[i] = p0[i] = (int32_t)v;
    }
    /* Everything a step can look up lies below the degree of the factors. */
    for (j = 0; j < nf; j++) {
        PyObject *f = PyTuple_GET_ITEM(factors, j);
        Py_ssize_t d;
        if (!PyTuple_CheckExact(f))
            goto use_python;
        d = PyTuple_GET_SIZE(f);
        if (n < 0)
            n = d;
        else if (n != d)
            goto use_python;
        for (i = 0; i < L; i++)
            if (g[i] >= n)
                goto use_python;
        if (!apply_tuple(g, L, f, n))
            goto use_python;
    }
    for (i = 0; i < L; i++)
        if (p0[i] > maxp)
            maxp = p0[i];
    if (maxp >= n)
        goto use_python;
    ok = ints_ensure(n);
    if (ok < 0)
        goto done;
    if (ok == 0)
        goto use_python;
    for (i = 0; i < ns; i++) {
        PyObject *step = PyList_GET_ITEM(steps, i), *t;
        Py_ssize_t l, k;
        int applied;
        if (!PyTuple_CheckExact(step) || PyTuple_GET_SIZE(step) != 2
            || !read_small(PyTuple_GET_ITEM(step, 0), &l) || l < 0
            || l >= PyList_GET_SIZE(Tis)
            || !read_index(PyTuple_GET_ITEM(step, 1), L, &k))
            goto use_python;
        if (g[k] == p0[k])
            continue;
        t = ti_lookup(PyList_GET_ITEM(Tis, l), g[k]);
        if (t == NULL) {
            if (PyErr_Occurred())
                goto done;
            res = Py_False;
            Py_INCREF(res);
            goto done;
        }
        applied = apply_tuple(g, L, t, n);
        Py_DECREF(t);
        if (!applied)
            goto use_python;
    }
    res = memcmp(g, p0, (size_t)L * sizeof(int32_t)) == 0 ? Py_True : Py_False;
    Py_INCREF(res);
    goto done;
use_python:
    res = Py_None;
    Py_INCREF(res);
done:
    if (g != sbuf)
        free(g);
    return res;
}

/* make_fast_plan(base, nt, start, amb, n) -> (points, steps); None to use the
 * reference. Keeps the order of the reference exactly. */
static PyObject *ck_make_fast_plan(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *base, *nt, *amb, *steps = NULL, *pts = NULL, *res = NULL;
    Py_ssize_t start, n, lo, hi, nnt, namb, nb, i, v, cnt = 0, nsteps, total;
    unsigned char *mark = NULL;
    PyObject **tmp = NULL;
    int ok;
    (void)m;
    if (nargs != 5 || !PyList_CheckExact(args[0]) || !PyList_CheckExact(args[1])
        || !read_small(args[2], &start) || !PyList_CheckExact(args[3])
        || !read_small(args[4], &n) || n < 0)
        Py_RETURN_NONE;
    base = args[0];
    nt = args[1];
    amb = args[3];
    nb = PyList_GET_SIZE(base);
    nnt = PyList_GET_SIZE(nt);
    namb = PyList_GET_SIZE(amb);
    ok = ints_ensure(nnt + namb + 2);
    if (ok < 0)
        return NULL;
    if (ok == 0)
        Py_RETURN_NONE;
    /* bisect_left(nt, start) */
    lo = 0;
    hi = nnt;
    while (lo < hi) {
        Py_ssize_t mid = lo + (hi - lo) / 2;
        if (!read_small(PyList_GET_ITEM(nt, mid), &v))
            Py_RETURN_NONE;
        if (v < start)
            lo = mid + 1;
        else
            hi = mid;
    }
    nsteps = nnt - lo;
    total = nsteps + namb + 1;
    mark = calloc((size_t)(n ? n : 1), 1);
    tmp = malloc((size_t)total * sizeof(PyObject *));
    steps = PyList_New(nsteps);
    if (mark == NULL || tmp == NULL) {
        PyErr_NoMemory();
        goto done;
    }
    if (steps == NULL)
        goto done;
    for (i = 0; i < nsteps; i++) {
        PyObject *lobj = PyList_GET_ITEM(nt, lo + i), *b, *pair;
        Py_ssize_t l, bv;
        if (!read_small(lobj, &l) || l < 0 || l >= nb)
            goto use_python;
        b = PyList_GET_ITEM(base, l);
        if (!read_index(b, n, &bv))
            goto use_python;
        mark[bv] = 1;
        pair = PyTuple_New(2);
        if (pair == NULL)
            goto done;
        Py_INCREF(lobj);
        PyTuple_SET_ITEM(pair, 0, lobj);
        PyTuple_SET_ITEM(pair, 1, int_ref(cnt));
        PyList_SET_ITEM(steps, i, pair);
        tmp[cnt++] = b;
    }
    for (i = 0; i < namb; i++) {
        PyObject *b = PyList_GET_ITEM(amb, i);
        Py_ssize_t bv;
        if (!read_index(b, n, &bv))
            goto use_python;
        if (!mark[bv]) {
            mark[bv] = 1;
            tmp[cnt++] = b;
        }
    }
    if (cnt == 0)                       /* the reference raises IndexError */
        goto use_python;
    if (cnt < 2) {                      /* (itemgetter needs two points) */
        Py_ssize_t f;
        if (!read_small(tmp[0], &f))
            goto use_python;
        tmp[cnt++] = ints_tab[f != 0 ? 0 : 1];
    }
    pts = PyTuple_New(cnt);
    if (pts == NULL)
        goto done;
    for (i = 0; i < cnt; i++) {
        Py_INCREF(tmp[i]);
        PyTuple_SET_ITEM(pts, i, tmp[i]);
    }
    res = PyTuple_New(2);
    if (res == NULL)
        goto done;
    PyTuple_SET_ITEM(res, 0, pts);
    PyTuple_SET_ITEM(res, 1, steps);
    pts = steps = NULL;
    goto done;
use_python:
    res = Py_None;
    Py_INCREF(res);
done:
    Py_XDECREF(pts);
    Py_XDECREF(steps);
    free(mark);
    free(tmp);
    return res;
}

/* -- 2-WL (refine.wl2_single) --------------------------------------------- */
typedef unsigned __int128 u128;
typedef struct { uint64_t a, b, c; } key3;

static inline int key_lt(const key3 *x, const key3 *y)
{
    if (x->a != y->a) return x->a < y->a;
    if (x->b != y->b) return x->b < y->b;
    return x->c < y->c;
}

static inline uint64_t key_hash(const key3 *k)
{
    uint64_t h = k->a * 0x9E3779B97F4A7C15ULL;
    h = (h ^ (h >> 29)) + k->b;
    h *= 0xBF58476D1CE4E5B9ULL;
    h = (h ^ (h >> 32)) + k->c;
    h *= 0x94D049BB133111EBULL;
    return h ^ (h >> 31);
}

/* Bottom-up merge sort of unique indices by their keys. */
static void sort_by_key(int32_t *idx, int32_t *tmp, Py_ssize_t m, const key3 *keys)
{
    Py_ssize_t w, i;
    int32_t *a = idx, *b = tmp;
    for (w = 1; w < m; w *= 2) {
        for (i = 0; i < m; i += 2 * w) {
            Py_ssize_t l = i, mid = i + w < m ? i + w : m;
            Py_ssize_t r = mid, end = i + 2 * w < m ? i + 2 * w : m, o = i;
            while (l < mid && r < end)
                b[o++] = key_lt(&keys[a[r]], &keys[a[l]]) ? a[r++] : a[l++];
            while (l < mid) b[o++] = a[l++];
            while (r < end) b[o++] = a[r++];
        }
        { int32_t *t = a; a = b; b = t; }
    }
    if (a != idx)
        memcpy(idx, a, (size_t)m * sizeof(int32_t));
}

/* Scratch for rank_keys, sized once for m items. */
typedef struct {
    int32_t *slots, *uid, *rep, *tmp, *rankof;
    size_t mask;
} rank_ws;

static int ws_init(rank_ws *w, Py_ssize_t m)
{
    size_t cap = 16;
    while (cap < 2 * (size_t)m)
        cap *= 2;
    w->mask = cap - 1;
    w->slots = malloc(cap * sizeof(int32_t));
    w->uid = malloc((size_t)m * sizeof(int32_t));
    w->rep = malloc((size_t)m * sizeof(int32_t));
    w->tmp = malloc((size_t)m * sizeof(int32_t));
    w->rankof = malloc((size_t)m * sizeof(int32_t));
    return w->slots && w->uid && w->rep && w->tmp && w->rankof;
}

static void ws_free(rank_ws *w)
{
    free(w->slots);
    free(w->uid);
    free(w->rep);
    free(w->tmp);
    free(w->rankof);
}

/* out[i] = the rank of keys[i] among the distinct keys, in increasing order;
 * returns the number of distinct keys. m must not exceed the ws_init size. */
static Py_ssize_t rank_keys(rank_ws *w, const key3 *keys, Py_ssize_t m, int32_t *out)
{
    Py_ssize_t i, u = 0;
    size_t mask = 15;
    while (mask + 1 < 2 * (size_t)m)    /* (w->mask is the size of the allocation) */
        mask = 2 * mask + 1;
    memset(w->slots, 0xff, (mask + 1) * sizeof(int32_t));
    for (i = 0; i < m; i++) {
        size_t s = (size_t)key_hash(&keys[i]) & mask;
        for (;;) {
            int32_t e = w->slots[s];
            if (e < 0) {
                w->slots[s] = (int32_t)u;
                w->uid[i] = (int32_t)u;
                w->rep[u] = (int32_t)i;
                u++;
                break;
            }
            {
                const key3 *o = &keys[w->rep[e]];
                if (o->a == keys[i].a && o->b == keys[i].b && o->c == keys[i].c) {
                    w->uid[i] = e;
                    break;
                }
            }
            s = (s + 1) & mask;
        }
    }
    sort_by_key(w->rep, w->tmp, u, keys);
    /* rep[pos] is now the item index of the key with rank pos */
    for (i = 0; i < u; i++)
        w->rankof[w->uid[w->rep[i]]] = (int32_t)i;
    for (i = 0; i < m; i++)
        out[i] = w->rankof[w->uid[i]];
    return u;
}

/* Reads `count` entries of the list `lst` into out; 0 with an exception set
 * (or with none if lst is not as expected). */
static int read_table(PyObject *lst, Py_ssize_t count, uint64_t *out)
{
    Py_ssize_t i;
    if (!PyList_CheckExact(lst) || PyList_GET_SIZE(lst) < count)
        return 0;
    for (i = 0; i < count; i++) {
        unsigned long long v = PyLong_AsUnsignedLongLong(PyList_GET_ITEM(lst, i));
        if (v == (unsigned long long)-1 && PyErr_Occurred())
            return 0;
        out[i] = v;
    }
    return 1;
}

/* Calls tables(size, n[, field_bits]) and copies count entries of U and V. */
static int get_tables(PyObject *tables, Py_ssize_t size, Py_ssize_t n, int field_bits,
                      Py_ssize_t cu, uint64_t *U, Py_ssize_t cv, uint64_t *V)
{
    PyObject *r, *a[3];
    int ok = 0;
    a[0] = PyLong_FromSsize_t(size);
    a[1] = PyLong_FromSsize_t(n);
    a[2] = field_bits ? PyLong_FromLong(field_bits) : NULL;
    if (!a[0] || !a[1] || (field_bits && !a[2])) {
        Py_XDECREF(a[0]);
        Py_XDECREF(a[1]);
        Py_XDECREF(a[2]);
        return 0;
    }
    r = PyObject_Vectorcall(tables, a, field_bits ? 3 : 2, NULL);
    Py_DECREF(a[0]);
    Py_DECREF(a[1]);
    Py_XDECREF(a[2]);
    if (r == NULL)
        return 0;
    if (PyTuple_CheckExact(r) && PyTuple_GET_SIZE(r) == 2)
        ok = read_table(PyTuple_GET_ITEM(r, 0), cu, U) && read_table(PyTuple_GET_ITEM(r, 1), cv, V);
    Py_DECREF(r);
    return ok;
}

/* The row sums of one 2-WL round: acc[j] = sum_k U[C(i, k)] V[C(k, j)] mod 2^128
 * for fixed i. Vr[k * n + j] = V[C(k, j)]; Tlo/Thi are the column sums of the
 * low 32 and high 32 bits of Vr. count is zeroed scratch of k colors. The
 * largest color class is handled through the column sums, as in the reference;
 * with many colors in the row the direct sum is cheaper. */
__attribute__((target_clones("avx2", "default")))
static void add_row_lohi(const uint64_t *row, uint64_t *lo, uint64_t *hi, Py_ssize_t n)
{
    Py_ssize_t j;
    for (j = 0; j < n; j++) {
        lo[j] += row[j] & 0xffffffffULL;
        hi[j] += row[j] >> 32;
    }
}

static void wl2_row(const int32_t *row, Py_ssize_t n, const uint64_t *U, const uint64_t *Vr,
                    const uint64_t *Tlo, const uint64_t *Thi, u128 *acc, int32_t *count,
                    int32_t *order, uint64_t *Slo, uint64_t *Shi)
{
    Py_ssize_t ncol = 0, k, j, best = 0, nonmajor;
    int32_t b = -1;
    for (k = 0; k < n; k++)
        if (count[row[k]]++ == 0)
            order[ncol++] = row[k];
    for (k = 0; k < ncol; k++)
        if (count[order[k]] > best) {
            best = count[order[k]];
            b = order[k];
        }
    nonmajor = n - best;
    if ((Py_ssize_t)(6 * (ncol - 1)) + nonmajor >= 2 * n) {
        /* direct sum: cheaper when the row has many colors */
        memset(acc, 0, (size_t)n * sizeof(u128));
        for (k = 0; k < n; k++) {
            uint64_t u = U[row[k]];
            const uint64_t *Vk = Vr + k * n;
            for (j = 0; j < n; j++)
                acc[j] += (u128)u * Vk[j];
        }
    } else {
        uint64_t ub = U[b];
        for (j = 0; j < n; j++)
            acc[j] = (u128)ub * ((u128)Tlo[j] + ((u128)Thi[j] << 32));
        /* One pass per color: S_a over the k with row[k] = a, then d * S_a. */
        for (k = 0; k < ncol; k++) {
            int32_t a = order[k];
            Py_ssize_t q;
            uint64_t d;
            if (a == b)
                continue;
            memset(Slo, 0, (size_t)n * sizeof(uint64_t));
            memset(Shi, 0, (size_t)n * sizeof(uint64_t));
            for (q = 0; q < n; q++)
                if (row[q] == a)
                    add_row_lohi(Vr + q * n, Slo, Shi, n);
            d = U[a] - ub;              /* wraps: arithmetic is mod 2^128 */
            {
                u128 ds = (u128)(__int128)(int64_t)d;
                for (j = 0; j < n; j++)
                    acc[j] += ds * ((u128)Slo[j] + ((u128)Shi[j] << 32));
            }
        }
    }
    for (k = 0; k < ncol; k++)
        count[order[k]] = 0;
}

#define WL2_MAX_N 4096

/* wl2_single(P, tables) -> (coloring, trace), the result of refine.wl2_single,
 * or None to use the reference (empty or unusually shaped input, values outside
 * the fast int range). */
static PyObject *ck_wl2_single(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *Pin, *tables, *trace = NULL, *t1 = NULL, *res = NULL, *outP = NULL;
    Py_ssize_t n, N, i, j, k, cap, v;
    int32_t *P = NULL, *ranks = NULL, *c = NULL, *c2 = NULL, *count = NULL, *order = NULL;
    key3 *keys = NULL;
    uint64_t *W = NULL, *Z = NULL, *cz = NULL, *Vr = NULL, *Tlo = NULL, *Thi = NULL,
             *Slo = NULL, *Shi = NULL, *U = NULL, *V = NULL;
    u128 *acc = NULL;
    rank_ws ws;
    (void)m;
    memset(&ws, 0, sizeof(ws));
    if (nargs != 2 || !PyList_CheckExact(args[0]))
        Py_RETURN_NONE;
    Pin = args[0];
    tables = args[1];
    n = PyList_GET_SIZE(Pin);
    if (n == 0 || n > WL2_MAX_N)
        Py_RETURN_NONE;
    N = n * n;
    cap = N > n ? N : n;
    P = malloc((size_t)N * sizeof(int32_t));
    ranks = malloc((size_t)N * sizeof(int32_t));
    c = malloc((size_t)n * sizeof(int32_t));
    c2 = malloc((size_t)n * sizeof(int32_t));
    keys = malloc((size_t)N * sizeof(key3));
    count = calloc((size_t)N + 1, sizeof(int32_t));
    order = malloc((size_t)n * sizeof(int32_t));
    W = malloc((size_t)cap * sizeof(uint64_t));
    Z = malloc((size_t)cap * sizeof(uint64_t));
    U = malloc((size_t)N * sizeof(uint64_t));
    V = malloc((size_t)N * sizeof(uint64_t));
    cz = malloc((size_t)n * sizeof(uint64_t));
    Vr = malloc((size_t)N * sizeof(uint64_t));
    Tlo = malloc((size_t)n * sizeof(uint64_t));
    Thi = malloc((size_t)n * sizeof(uint64_t));
    Slo = malloc((size_t)n * sizeof(uint64_t));
    Shi = malloc((size_t)n * sizeof(uint64_t));
    acc = malloc((size_t)n * sizeof(u128));
    if (!P || !ranks || !c || !c2 || !keys || !count || !order || !W || !Z || !U || !V
        || !cz || !Vr || !Tlo || !Thi || !Slo || !Shi || !acc || !ws_init(&ws, N)) {
        PyErr_NoMemory();
        goto done;
    }
    /* read the matrix; rows of any exact sequence of exact small ints */
    for (i = 0; i < n; i++) {
        PyObject *row = PyList_GET_ITEM(Pin, i);
        if (!(PyList_CheckExact(row) || PyTuple_CheckExact(row))
            || PySequence_Fast_GET_SIZE(row) != n)
            goto use_python;
        for (j = 0; j < n; j++) {
            if (!read_small(PySequence_Fast_GET_ITEM(row, j), &v))
                goto use_python;
            P[i * n + j] = (int32_t)v;
        }
    }
    trace = PyList_New(0);
    if (trace == NULL)
        goto done;
    /* names = rank in the sorted set of values */
    for (i = 0; i < N; i++) {
        keys[i].a = (uint64_t)((int64_t)P[i] + ((int64_t)1 << 32));
        keys[i].b = keys[i].c = 0;
    }
    k = rank_keys(&ws, keys, N, P);
#define APPEND_INT(x) do { PyObject *_o = PyLong_FromSsize_t(x); \
        if (_o == NULL || PyList_Append(trace, _o) < 0) { Py_XDECREF(_o); goto done; } \
        Py_DECREF(_o); } while (0)
    APPEND_INT(k);
    for (;;) {
        Py_ssize_t mcls, t1_last, mm, nt1;
        if (PyErr_CheckSignals() < 0)   /* a bench timeout must be able to fire */
            goto done;
        /* 1-WL on the vertices */
        if (!get_tables(tables, k > n ? k : n, n, 63, k > n ? k : n, W, k > n ? k : n, Z)) {
            if (!PyErr_Occurred())
                goto use_python;
            goto done;
        }
        for (i = 0; i < n; i++) {
            keys[i].a = (uint64_t)P[i * n + i];
            keys[i].b = keys[i].c = 0;
        }
        mcls = rank_keys(&ws, keys, n, c);
        Py_XDECREF(t1);
        t1 = PyList_New(0);
        if (t1 == NULL)
            goto done;
#define APPEND_T1(x) do { PyObject *_o = PyLong_FromSsize_t(x); \
        if (_o == NULL || PyList_Append(t1, _o) < 0) { Py_XDECREF(_o); goto done; } \
        Py_DECREF(_o); } while (0)
        APPEND_T1(mcls);
        while (mcls < n) {
            for (j = 0; j < n; j++)
                cz[j] = Z[c[j]];
            for (i = 0; i < n; i++) {
                uint64_t s = 0;
                const int32_t *row = P + i * n;
                for (j = 0; j < n; j++)
                    s += W[row[j]] * cz[j];
                keys[i].a = (uint64_t)c[i];
                keys[i].b = s;
                keys[i].c = 0;
            }
            mm = rank_keys(&ws, keys, n, c2);
            if (mm == mcls)
                break;
            memcpy(c, c2, (size_t)n * sizeof(int32_t));
            mcls = mm;
            APPEND_T1(mcls);
        }
        nt1 = PyList_GET_SIZE(t1);
        t1_last = mcls;
        {
            PyObject *tup = PyList_AsTuple(t1);
            if (tup == NULL || PyList_Append(trace, tup) < 0) {
                Py_XDECREF(tup);
                goto done;
            }
            Py_DECREF(tup);
        }
        if (nt1 > 1 || (t1_last == n && k < N)) {
            /* fold the vertex colors into the pair colors */
            for (i = 0; i < n; i++)
                for (j = 0; j < n; j++) {
                    keys[i * n + j].a = (((uint64_t)c[i] * (uint64_t)n + (uint64_t)c[j])
                                         * (uint64_t)k) + (uint64_t)P[i * n + j];
                    keys[i * n + j].b = keys[i * n + j].c = 0;
                }
            k = rank_keys(&ws, keys, N, P);
            APPEND_INT(k);
        }
        if (k == N || t1_last == n)
            break;
        /* one 2-WL round */
        if (!get_tables(tables, k, n, 0, k, U, k, V)) {
            if (!PyErr_Occurred())
                goto use_python;
            goto done;
        }
        memset(Tlo, 0, (size_t)n * sizeof(uint64_t));
        memset(Thi, 0, (size_t)n * sizeof(uint64_t));
        for (i = 0; i < N; i++)
            Vr[i] = V[P[i]];
        for (i = 0; i < n; i++)
            add_row_lohi(Vr + i * n, Tlo, Thi, n);
        for (i = 0; i < n; i++) {
            const int32_t *row = P + i * n;
            wl2_row(row, n, U, Vr, Tlo, Thi, acc, count, order, Slo, Shi);
            for (j = 0; j < n; j++) {
                keys[i * n + j].a = (uint64_t)row[j];
                keys[i * n + j].b = (uint64_t)(acc[j] >> 64);
                keys[i * n + j].c = (uint64_t)acc[j];
            }
        }
        {
            Py_ssize_t ku = rank_keys(&ws, keys, N, ranks);
            if (ku == k)                /* the keys refine the old colors: stable */
                break;
            memcpy(P, ranks, (size_t)N * sizeof(int32_t));
            k = ku;
            APPEND_INT(k);
        }
    }
    /* output */
    outP = PyList_New(n);
    if (outP == NULL)
        goto done;
    for (i = 0; i < n; i++) {
        PyObject *row = PyList_New(n);
        if (row == NULL)
            goto done;
        PyList_SET_ITEM(outP, i, row);
        for (j = 0; j < n; j++) {
            PyObject *o = PyLong_FromLong(P[i * n + j]);
            if (o == NULL)
                goto done;
            PyList_SET_ITEM(row, j, o);
        }
    }
    {
        PyObject *tr = PyList_AsTuple(trace);
        if (tr == NULL)
            goto done;
        res = PyTuple_New(2);
        if (res == NULL) {
            Py_DECREF(tr);
            goto done;
        }
        Py_INCREF(outP);
        PyTuple_SET_ITEM(res, 0, outP);
        PyTuple_SET_ITEM(res, 1, tr);
    }
    goto done;
use_python:
    PyErr_Clear();
    res = Py_None;
    Py_INCREF(res);
done:
    Py_XDECREF(trace);
    Py_XDECREF(t1);
    Py_XDECREF(outP);
    free(P); free(ranks); free(c); free(c2); free(keys); free(count); free(order);
    free(W); free(Z); free(U); free(V); free(cz); free(Vr); free(Tlo); free(Thi);
    free(Slo); free(Shi); free(acc);
    ws_free(&ws);
    return res;
}

/* Reads an n x n list of lists of small ints into out; 0 if it is not one. */
static int read_matrix(PyObject *P, Py_ssize_t n, int32_t *out)
{
    Py_ssize_t i, j, v;
    if (!PyList_CheckExact(P) || PyList_GET_SIZE(P) != n)
        return 0;
    for (i = 0; i < n; i++) {
        PyObject *row = PyList_GET_ITEM(P, i);
        if (!(PyList_CheckExact(row) || PyTuple_CheckExact(row))
            || PySequence_Fast_GET_SIZE(row) != n)
            return 0;
        for (j = 0; j < n; j++) {
            if (!read_small(PySequence_Fast_GET_ITEM(row, j), &v))
                return 0;
            out[i * n + j] = (int32_t)v;
        }
    }
    return 1;
}

/* wl2_check(PX, PY, RX, RY): the final test of refine.wl2 (one function from
 * refined to input colors on both sides, and equal histograms of the refined
 * colors). RY is RX means the X side only. None to use the reference. */
static PyObject *ck_wl2_check(PyObject *m, PyObject *const *args, Py_ssize_t nargs)
{
    Py_ssize_t n, N, i;
    int32_t *px = NULL, *rx = NULL, *py = NULL, *ry = NULL, *first = NULL, *cnt = NULL;
    unsigned char *seen = NULL;
    PyObject *res = NULL;
    int same;
    (void)m;
    if (nargs != 4 || !PyList_CheckExact(args[0]))
        Py_RETURN_NONE;
    n = PyList_GET_SIZE(args[0]);
    if (n == 0 || n > WL2_MAX_N)
        Py_RETURN_NONE;
    N = n * n;
    same = args[2] == args[3];
    px = malloc((size_t)N * sizeof(int32_t));
    rx = malloc((size_t)N * sizeof(int32_t));
    py = malloc((size_t)N * sizeof(int32_t));
    ry = malloc((size_t)N * sizeof(int32_t));
    first = malloc((size_t)N * sizeof(int32_t));
    cnt = calloc((size_t)N, sizeof(int32_t));
    seen = calloc((size_t)N, 1);
    if (!px || !rx || !py || !ry || !first || !cnt || !seen) {
        PyErr_NoMemory();
        goto done;
    }
    if (!read_matrix(args[0], n, px) || !read_matrix(args[2], n, rx)
        || (!same && (!read_matrix(args[1], n, py) || !read_matrix(args[3], n, ry))))
        goto use_python;
    for (i = 0; i < N; i++)             /* a refined color outside range(N) is not ours */
        if (rx[i] < 0 || rx[i] >= N || (!same && (ry[i] < 0 || ry[i] >= N)))
            goto use_python;
    for (i = 0; i < N; i++) {
        int32_t r = rx[i];
        if (seen[r]) {
            if (first[r] != px[i])
                goto no;
        } else {
            seen[r] = 1;
            first[r] = px[i];
        }
        cnt[r]++;
    }
    if (!same) {
        for (i = 0; i < N; i++) {
            int32_t r = ry[i];
            if (seen[r]) {
                if (first[r] != py[i])
                    goto no;
            } else {
                seen[r] = 1;
                first[r] = py[i];
            }
            cnt[r]--;
        }
        for (i = 0; i < N; i++)
            if (cnt[i] != 0)
                goto no;
    }
    res = Py_True;
    Py_INCREF(res);
    goto done;
no:
    res = Py_False;
    Py_INCREF(res);
    goto done;
use_python:
    res = Py_None;
    Py_INCREF(res);
done:
    free(px); free(rx); free(py); free(ry); free(first); free(cnt); free(seen);
    return res;
}

/* -- module --------------------------------------------------------------- */
#define FAST(name) {#name, (PyCFunction)(void (*)(void))ck_##name, METH_FASTCALL, NULL}
static PyMethodDef methods[] = {
    FAST(set_fallbacks), FAST(mul), FAST(inv), FAST(act), FAST(maps), FAST(orbits),
    FAST(sift), FAST(sifts_to_id), FAST(make_fast_plan), FAST(wl2_single), FAST(wl2_check),
    {NULL, NULL, 0, NULL}
};

static struct PyModuleDef moddef = {
    PyModuleDef_HEAD_INIT, "_ckernel",
    "Optional compiled kernel of gi; see gi/_ckernel.c and docs/w16-ckernel.md.", -1, methods,
    NULL, NULL, NULL, NULL
};

PyMODINIT_FUNC PyInit__ckernel(void)
{
    PyObject *mod = PyModule_Create(&moddef);
    if (mod == NULL)
        return NULL;
    str_get = PyUnicode_InternFromString("get");
    if (str_get == NULL
        || PyModule_AddIntConstant(mod, "API_VERSION", CK_API_VERSION) < 0
        || PyModule_AddStringConstant(mod, "SOURCE_HASH", CK_SOURCE_HASH) < 0) {
        Py_DECREF(mod);
        return NULL;
    }
    return mod;
}
