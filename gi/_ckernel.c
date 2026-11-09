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
/* ===== w23-speed2: bounded-degree and canonical-labeling paths (gi/wl.py,
 * gi/bounded.py, gi/canon.py); see docs/w23-speed2.md. Same contract as above:
 * exactly the semantics of the Python reference, which stays the fallback;
 * unusual input is declined before any Python-visible state is changed.
 * ======================================================================== */

/* Sorts m keys ascending; tmp has room for m keys. */
static void sort_u64(uint64_t *a, uint64_t *tmp, Py_ssize_t m)
{
    if (m < 96) {                       /* insertion sort */
        Py_ssize_t i, j;
        for (i = 1; i < m; i++) {
            uint64_t x = a[i];
            for (j = i; j > 0 && a[j - 1] > x; j--)
                a[j] = a[j - 1];
            a[j] = x;
        }
        return;
    }
    {                                   /* LSD radix sort, 11-bit digits */
        uint64_t *src = a, *dst = tmp, *t;
        int pass, shift;
        for (pass = 0, shift = 0; pass < 6; pass++, shift += 11) {
            Py_ssize_t count[2048], sum = 0, i;
            memset(count, 0, sizeof(count));
            for (i = 0; i < m; i++)
                count[(src[i] >> shift) & 2047]++;
            if (count[(src[0] >> shift) & 2047] == m)
                continue;               /* all keys have this digit */
            for (i = 0; i < 2048; i++) {
                Py_ssize_t c = count[i];
                count[i] = sum;
                sum += c;
            }
            for (i = 0; i < m; i++)
                dst[count[(src[i] >> shift) & 2047]++] = src[i];
            t = src; src = dst; dst = t;
        }
        if (src != a)
            memcpy(a, src, (size_t)m * sizeof(uint64_t));
    }
}

/* Reads nbr, a list of n lists or tuples of exact ints in [0, n), into CSR form
 * (off has n + 1 entries, adj the concatenated rows). strict: every row must be
 * strictly increasing. Returns 1 (the caller frees *offp and *adjp), 0 for
 * unusual input, -1 with an exception set. */
static int read_adj(PyObject *nbr, Py_ssize_t n, int strict, int32_t **offp, int32_t **adjp)
{
    Py_ssize_t v, j, m = 0, x;
    int32_t *off, *adj;
    for (v = 0; v < n; v++) {
        PyObject *row = PyList_GET_ITEM(nbr, v);
        if (!PyList_CheckExact(row) && !PyTuple_CheckExact(row))
            return 0;
        m += PySequence_Fast_GET_SIZE(row);
        if (m > INT32_MAX - 1)
            return 0;
    }
    off = malloc((size_t)(n + 1) * sizeof(int32_t));
    adj = malloc((size_t)(m ? m : 1) * sizeof(int32_t));
    if (!off || !adj) {
        free(off);
        free(adj);
        PyErr_NoMemory();
        return -1;
    }
    m = 0;
    for (v = 0; v < n; v++) {
        PyObject *row = PyList_GET_ITEM(nbr, v);
        Py_ssize_t len = PySequence_Fast_GET_SIZE(row);
        off[v] = (int32_t)m;
        for (j = 0; j < len; j++) {
            if (!read_index(PySequence_Fast_GET_ITEM(row, j), n, &x)
                || (strict && j > 0 && adj[m + j - 1] >= (int32_t)x)) {
                free(off);
                free(adj);
                return 0;
            }
            adj[m + j] = (int32_t)x;
        }
        m += len;
    }
    off[n] = (int32_t)m;
    *offp = off;
    *adjp = adj;
    return 1;
}

/* A list of n exact ints below 2^30 in absolute value, into out[]; 0 if not. */
static int read_ints(PyObject *seq, Py_ssize_t n, int32_t *out)
{
    Py_ssize_t i, v;
    if ((!PyList_CheckExact(seq) && !PyTuple_CheckExact(seq))
        || PySequence_Fast_GET_SIZE(seq) != n)
        return 0;
    for (i = 0; i < n; i++) {
        if (!read_small(PySequence_Fast_GET_ITEM(seq, i), &v))
            return 0;
        out[i] = (int32_t)v;
    }
    return 1;
}

/* Worklist 1-WL, gi.wl.refine: the same result, cell for cell (see its
 * docstring: every decision depends on sizes, counts and colors only, so the
 * order in which a cell's members are visited does not matter). Cells are
 * ranges of lab; cid[v] names the cell of v; new names are handed out exactly
 * as in Python. refine(nbr, col, roots, stable) -> list of names, or None. */
#define WLR_MAX ((Py_ssize_t)1 << 21)   /* for the sort keys below */
static PyObject *ck_wl_refine(PyObject *m_, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *nbr, *res = NULL;
    Py_ssize_t n, nr = 0, v, i, j, ok, m;
    int32_t *off = NULL, *adj = NULL, *col = NULL, *lab = NULL, *pos = NULL, *cid = NULL,
            *cstart = NULL, *csize = NULL, *queue = NULL, *cnt = NULL, *T = NULL, *roots = NULL;
    uint64_t *keys = NULL, *tmp = NULL;
    Py_ssize_t ncell = 0, qh = 0, qt = 0;
    int64_t minc;
    int stable;
    (void)m_;
    if (nargs != 4 || !PyList_CheckExact(args[0]))
        Py_RETURN_NONE;
    nbr = args[0];
    n = PyList_GET_SIZE(nbr);
    if (n >= WLR_MAX)
        Py_RETURN_NONE;
    if (args[3] == Py_True)
        stable = 1;
    else if (args[3] == Py_False)
        stable = 0;
    else
        Py_RETURN_NONE;
    if (!PyTuple_CheckExact(args[2]) && !PyList_CheckExact(args[2]))
        Py_RETURN_NONE;
    nr = PySequence_Fast_GET_SIZE(args[2]);
    if (n == 0) {
        if (nr)                         /* (a root in an empty graph: Python decides) */
            Py_RETURN_NONE;
        if (!PyList_CheckExact(args[1]) && !PyTuple_CheckExact(args[1]))
            Py_RETURN_NONE;
        if (PySequence_Fast_GET_SIZE(args[1]) != 0)
            Py_RETURN_NONE;
        return PyList_New(0);
    }
    ok = read_adj(nbr, n, 0, &off, &adj);
    if (ok < 0)
        return NULL;
    if (ok == 0)
        Py_RETURN_NONE;
    m = off[n];
    if (m >= WLR_MAX) {
        res = Py_None;
        Py_INCREF(res);
        goto done;
    }
    col = malloc((size_t)n * sizeof(int32_t));
    lab = malloc((size_t)n * sizeof(int32_t));
    pos = malloc((size_t)n * sizeof(int32_t));
    cid = malloc((size_t)n * sizeof(int32_t));
    cstart = malloc((size_t)(n + 1) * sizeof(int32_t));
    csize = malloc((size_t)(n + 1) * sizeof(int32_t));
    queue = malloc((size_t)(2 * n + 2) * sizeof(int32_t));
    cnt = calloc((size_t)n, sizeof(int32_t));
    T = malloc((size_t)n * sizeof(int32_t));
    keys = malloc((size_t)n * sizeof(uint64_t));
    tmp = malloc((size_t)n * sizeof(uint64_t));
    roots = malloc((size_t)(nr ? nr : 1) * sizeof(int32_t));
    if (!col || !lab || !pos || !cid || !cstart || !csize || !queue || !cnt || !T || !keys || !tmp
        || !roots) {
        PyErr_NoMemory();
        goto done;
    }
    if (!read_ints(args[1], n, col)) {
        res = Py_None;
        Py_INCREF(res);
        goto done;
    }
    for (i = 0; i < nr; i++) {
        Py_ssize_t r;
        if (!read_index(PySequence_Fast_GET_ITEM(args[2], i), n, &r)) {
            res = Py_None;
            Py_INCREF(res);
            goto done;
        }
        roots[i] = (int32_t)r;
    }
    /* initial cells: the colors in increasing order */
    minc = col[0];
    for (v = 1; v < n; v++)
        if (col[v] < minc)
            minc = col[v];
    for (v = 0; v < n; v++)
        keys[v] = ((uint64_t)((int64_t)col[v] - minc) << 21) | (uint64_t)v;
    sort_u64(keys, tmp, n);
    for (i = 0; i < n; ) {
        uint64_t c = keys[i] >> 21;
        j = i;
        while (j < n && keys[j] >> 21 == c) {
            int32_t w = (int32_t)(keys[j] & (((uint64_t)1 << 21) - 1));
            lab[j] = w;
            pos[w] = (int32_t)j;
            cid[w] = (int32_t)ncell;
            j++;
        }
        cstart[ncell] = (int32_t)i;
        csize[ncell] = (int32_t)(j - i);
        ncell++;
        i = j;
    }
    if (!stable)
        for (i = 0; i < ncell; i++)
            queue[qt++] = (int32_t)i;
    for (i = 0; i < nr; i++) {
        int32_t r = roots[i], c = cid[r];
        if (csize[c] > 1) {
            int32_t last = cstart[c] + csize[c] - 1, pr = pos[r], a = lab[last];
            lab[last] = r; pos[r] = last;
            lab[pr] = a; pos[a] = pr;
            csize[c]--;
            cstart[ncell] = last;
            csize[ncell] = 1;
            cid[r] = (int32_t)ncell;
            queue[qt++] = (int32_t)ncell;
            ncell++;
        }
    }
    {
        Py_ssize_t pops = 0;
        while (qh < qt) {
            int32_t C = queue[qh++];
            Py_ssize_t nT = 0, ti, a, e;
            if ((++pops & 0x3fff) == 0 && PyErr_CheckSignals() < 0)
                goto done;
            a = cstart[C];
            e = a + csize[C];
            for (i = a; i < e; i++) {
                int32_t u = lab[i];
                for (j = off[u]; j < off[u + 1]; j++) {
                    int32_t w = adj[j];
                    if (cnt[w] == 0)
                        T[nT++] = w;
                    cnt[w]++;
                }
            }
            for (i = 0; i < nT; i++) {
                int32_t w = T[i];
                keys[i] = ((uint64_t)cid[w] << 42) | ((uint64_t)cnt[w] << 21) | (uint64_t)w;
            }
            sort_u64(keys, tmp, nT);
            for (ti = 0; ti < nT; ) {
                uint64_t D64 = keys[ti] >> 42;
                int32_t D = (int32_t)D64, s = cstart[D], size = csize[D];
                Py_ssize_t tj = ti, tvlen, rest, big = -1, bigsize, p, q, nparts = 0, ps;
                uint64_t pcnt;
                while (tj < nT && keys[tj] >> 42 == D64)
                    tj++;
                tvlen = tj - ti;
                rest = size - tvlen;
                /* parts: runs of equal count (keys are sorted) */
                pcnt = ~(uint64_t)0;
                for (i = ti; i < tj; i++) {
                    uint64_t c = (keys[i] >> 21) & (((uint64_t)1 << 21) - 1);
                    if (c != pcnt) {
                        nparts++;
                        pcnt = c;
                    }
                }
                if (nparts == 1 && tvlen == size) {
                    ti = tj;
                    continue;
                }
                bigsize = rest;
                {
                    Py_ssize_t idx = -1, count = 0;
                    pcnt = ~(uint64_t)0;
                    for (i = ti; i <= tj; i++) {
                        uint64_t c = i < tj ? (keys[i] >> 21) & (((uint64_t)1 << 21) - 1)
                                            : ~(uint64_t)0;
                        if (c != pcnt) {
                            if (idx >= 0 && count > bigsize) {
                                big = idx;
                                bigsize = count;
                            }
                            idx++;
                            count = 0;
                            pcnt = c;
                        }
                        count++;
                    }
                }
                /* the touched vertices to the tail, in key order */
                {
                    Py_ssize_t idx, tail = s + size;
                    for (idx = tj - 1; idx >= ti; idx--) {
                        int32_t w = (int32_t)(keys[idx] & (((uint64_t)1 << 21) - 1));
                        int32_t pw = pos[w], x;
                        tail--;
                        x = lab[tail];
                        lab[tail] = w;
                        pos[w] = (int32_t)tail;
                        lab[pw] = x;
                        pos[x] = pw;
                    }
                }
                ps = s + rest;
                if (big < 0) {
                    csize[D] = (int32_t)rest;   /* the untouched part keeps the name */
                } else if (rest) {
                    int32_t nw = (int32_t)ncell++;
                    cstart[nw] = s;
                    csize[nw] = (int32_t)rest;
                    for (q = s; q < s + rest; q++)
                        cid[lab[q]] = nw;
                    queue[qt++] = nw;
                }
                /* the parts, ascending by count */
                {
                    Py_ssize_t idx = ti;
                    for (p = 0; p < nparts; p++) {
                        uint64_t c = (keys[idx] >> 21) & (((uint64_t)1 << 21) - 1);
                        Py_ssize_t idx2 = idx;
                        while (idx2 < tj && ((keys[idx2] >> 21) & (((uint64_t)1 << 21) - 1)) == c)
                            idx2++;
                        if (p == big) {
                            cstart[D] = (int32_t)ps;
                            csize[D] = (int32_t)(idx2 - idx);
                        } else {
                            int32_t nw = (int32_t)ncell++;
                            cstart[nw] = (int32_t)ps;
                            csize[nw] = (int32_t)(idx2 - idx);
                            for (q = 0; q < idx2 - idx; q++)
                                cid[lab[ps + q]] = nw;
                            queue[qt++] = nw;
                        }
                        ps += idx2 - idx;
                        idx = idx2;
                    }
                }
                ti = tj;
            }
            for (i = 0; i < nT; i++)
                cnt[T[i]] = 0;
        }
    }
    ok = ints_ensure(n);
    if (ok < 0)
        goto done;
    if (ok == 0) {                      /* (too large for the table: box each) */
        res = PyList_New(n);
        if (res == NULL)
            goto done;
        for (v = 0; v < n; v++) {
            PyObject *o = PyLong_FromSsize_t(cid[v]);
            if (o == NULL) {
                Py_CLEAR(res);
                goto done;
            }
            PyList_SET_ITEM(res, v, o);
        }
        goto done;
    }
    res = PyList_New(n);
    if (res == NULL)
        goto done;
    for (v = 0; v < n; v++)
        PyList_SET_ITEM(res, v, int_ref(cid[v]));
done:
    free(off); free(adj); free(col); free(lab); free(pos); free(cid); free(cstart);
    free(csize); free(queue); free(cnt); free(T); free(keys); free(tmp); free(roots);
    return res;
}

/* Merge sort of idx[0..s) by the up-sets (uplen, upstart into upbuf), compared
 * by (length, entries): an exact order, so equal sets end up adjacent. */
static inline int upset_lt(const int32_t *uplen, const int32_t *upstart, const int32_t *upbuf,
                           int32_t a, int32_t b)
{
    int32_t k, la = uplen[a], lb = uplen[b];
    if (la != lb)
        return la < lb;
    for (k = 0; k < la; k++) {
        int32_t x = upbuf[upstart[a] + k], y = upbuf[upstart[b] + k];
        if (x != y)
            return x < y;
    }
    return 0;
}

static void sort_upsets(int32_t *idx, int32_t *tmp, Py_ssize_t s, const int32_t *uplen,
                        const int32_t *upstart, const int32_t *upbuf)
{
    Py_ssize_t w, i, j, k, lo, mid, hi;
    int32_t *src = idx, *dst = tmp, *t;
    for (w = 1; w < s; w *= 2) {
        for (lo = 0; lo < s; lo += 2 * w) {
            mid = lo + w < s ? lo + w : s;
            hi = lo + 2 * w < s ? lo + 2 * w : s;
            i = lo;
            j = mid;
            k = lo;
            while (i < mid && j < hi) {
                if (upset_lt(uplen, upstart, upbuf, src[j], src[i]))
                    dst[k++] = src[j++];
                else
                    dst[k++] = src[i++];
            }
            while (i < mid)
                dst[k++] = src[i++];
            while (j < hi)
                dst[k++] = src[j++];
        }
        t = src; src = dst; dst = t;
    }
    if (src != idx)
        memcpy(idx, src, (size_t)s * sizeof(int32_t));
}

/* gi.bounded.class_plan on int colors in [0, n): the same plan.
 * class_plan(nbr, col, u0, u1) -> plan (a list of lists of colors), None (BFS),
 * or NotImplemented when the input is unusual (the Python body runs). */
static PyObject *ck_class_plan(PyObject *m_, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *nbr, *colobj, *plan = NULL;
    Py_ssize_t n, v, i, j, k, ok, u0_, u1_;
    int32_t *off = NULL, *adj = NULL, *col = NULL, *mstart = NULL, *memb = NULL,
            *plist = NULL, *pidx = NULL, *upbuf = NULL, *uplen = NULL, *upstart = NULL,
            *idx = NULL, *itmp = NULL, *dlist = NULL, *dets = NULL, *spairs = NULL, *layer = NULL;
    int64_t *near = NULL;
    uint8_t *done = NULL, *pend = NULL, *dirty = NULL, *shas = NULL, *sbig3 = NULL,
            *srisk = NULL, *det = NULL;
    Py_ssize_t npend = 0, ndirty = 0, ndet = 0;
    (void)m_;
    if (nargs != 4 || !PyList_CheckExact(args[0]))
        Py_RETURN_NOTIMPLEMENTED;
    nbr = args[0];
    colobj = args[1];
    n = PyList_GET_SIZE(nbr);
    if (n == 0 || !read_index(args[2], n, &u0_) || !read_index(args[3], n, &u1_))
        Py_RETURN_NOTIMPLEMENTED;
    ok = read_adj(nbr, n, 1, &off, &adj);
    if (ok < 0)
        return NULL;
    if (ok == 0)
        Py_RETURN_NOTIMPLEMENTED;
    col = malloc((size_t)n * sizeof(int32_t));
    mstart = calloc((size_t)n + 2, sizeof(int32_t));
    memb = malloc((size_t)n * sizeof(int32_t));
    plist = malloc((size_t)n * sizeof(int32_t));
    pidx = malloc((size_t)n * sizeof(int32_t));
    upbuf = malloc((size_t)(off[n] ? off[n] : 1) * sizeof(int32_t));
    uplen = malloc((size_t)n * sizeof(int32_t));
    upstart = malloc((size_t)n * sizeof(int32_t));
    idx = malloc((size_t)n * sizeof(int32_t));
    itmp = malloc((size_t)n * sizeof(int32_t));
    dlist = malloc((size_t)n * sizeof(int32_t));
    dets = malloc((size_t)n * sizeof(int32_t));
    spairs = calloc((size_t)n, sizeof(int32_t));
    layer = malloc((size_t)n * sizeof(int32_t));
    near = calloc((size_t)n, sizeof(int64_t));
    done = calloc((size_t)n, 1);
    pend = calloc((size_t)n, 1);
    dirty = calloc((size_t)n, 1);
    shas = calloc((size_t)n, 1);
    sbig3 = calloc((size_t)n, 1);
    srisk = calloc((size_t)n, 1);
    det = calloc((size_t)n, 1);
    if (!col || !mstart || !memb || !plist || !pidx || !upbuf || !uplen || !upstart || !idx
        || !itmp || !dlist || !dets || !spairs || !layer || !near || !done || !pend || !dirty
        || !shas || !sbig3 || !srisk || !det) {
        PyErr_NoMemory();
        goto done;
    }
    ok = ints_ensure(n);
    if (ok < 0)
        goto done;
    if (ok == 0 || !read_ints(colobj, n, col)) {
        plan = Py_NotImplemented;
        Py_INCREF(plan);
        goto done;
    }
    for (v = 0; v < n; v++) {
        if (col[v] < 0 || col[v] >= n) {
            plan = Py_NotImplemented;
            Py_INCREF(plan);
            goto done;
        }
        mstart[col[v] + 1]++;
    }
    for (i = 0; i < n; i++)
        mstart[i + 1] += mstart[i];
    {
        int32_t *fill = malloc((size_t)(n + 1) * sizeof(int32_t));
        if (!fill) {
            PyErr_NoMemory();
            goto done;
        }
        memcpy(fill, mstart, (size_t)(n + 1) * sizeof(int32_t));
        for (v = 0; v < n; v++)
            memb[fill[col[v]]++] = (int32_t)v;
        free(fill);
    }
    /* pending = the colors present, minus the colors of the roots */
    for (i = 0; i < n; i++) {
        if (mstart[i + 1] > mstart[i] && (int32_t)i != col[u0_] && (int32_t)i != col[u1_]) {
            pend[i] = 1;
            pidx[i] = (int32_t)npend;
            plist[npend++] = (int32_t)i;
        }
    }
#define PLACED(v_) do { \
        int32_t v__ = (v_), j__, l__; \
        for (j__ = off[v__]; j__ < off[v__ + 1]; j__++) { \
            int32_t w__ = adj[j__], c__ = col[w__]; \
            if (!dirty[c__]) { dirty[c__] = 1; dlist[ndirty++] = c__; } \
            for (l__ = off[w__]; l__ < off[w__ + 1]; l__++) \
                near[col[adj[l__]]]++; \
        } \
    } while (0)
    done[u0_] = 1;
    done[u1_] = 1;
    PLACED(u0_);
    PLACED(u1_);
    for (i = 0; i < npend; i++) {       /* dirty |= pending */
        int32_t c = plist[i];
        if (!dirty[c]) {
            dirty[c] = 1;
            dlist[ndirty++] = c;
        }
    }
    plan = PyList_New(0);
    if (plan == NULL)
        goto done;
    while (npend > 0) {
        Py_ssize_t nlayer = 0;
        PyObject *lay;
        for (i = 0; i < ndirty; i++) {
            int32_t c = dlist[i], s0 = mstart[c], s = mstart[c + 1] - s0;
            Py_ssize_t big;
            dirty[c] = 0;
            if (!pend[c])
                continue;
            if (s == 1) {
                big = 1;
            } else {
                Py_ssize_t q, r, tot = 0;
                for (q = 0; q < s; q++) {
                    int32_t u = memb[s0 + q], l = 0, a;
                    upstart[q] = (int32_t)tot;
                    for (a = off[u]; a < off[u + 1]; a++)
                        if (done[adj[a]]) {
                            upbuf[tot++] = adj[a];
                            l++;
                        }
                    uplen[q] = l;
                    idx[q] = (int32_t)q;
                }
                sort_upsets(idx, itmp, s, uplen, upstart, upbuf);
                big = 0;
                {
                    int risk = 0;
                    int32_t pairs = 0;
                    q = 0;
                    while (q < s) {
                        r = q + 1;
                        while (r < s && !upset_lt(uplen, upstart, upbuf, idx[q], idx[r]))
                            r++;
                        {
                            int32_t kk = (int32_t)(r - q);
                            if (kk > big)
                                big = kk;
                            if (kk >= 2) {
                                if (uplen[idx[q]] > 0)
                                    risk = 1;
                                pairs += kk;
                            }
                        }
                        q = r;
                    }
                    if (big > 1) {
                        shas[c] = 1;
                        sbig3[c] = big >= 3;
                        srisk[c] = (uint8_t)risk;
                        spairs[c] = pairs;
                        det[c] = 0;
                        continue;
                    }
                }
            }
            /* big == 1 */
            if (!det[c]) {
                det[c] = 1;
                dets[ndet++] = c;
            }
            shas[c] = 0;
        }
        ndirty = 0;
        {
            Py_ssize_t nd = 0;
            for (j = 0; j < ndet; j++)
                if (det[dets[j]]) {
                    int32_t x = dets[j], l2 = (int32_t)nd;
                    while (l2 > 0 && layer[l2 - 1] > x) {   /* insertion sort */
                        layer[l2] = layer[l2 - 1];
                        l2--;
                    }
                    layer[l2] = x;
                    nd++;
                }
            nlayer = nd;
        }
        if (nlayer > 0) {
            for (j = 0; j < nlayer; j++)
                det[layer[j]] = 0;
            ndet = 0;
        } else {
            int32_t bestc = -1;
            for (j = 0; j < npend; j++) {
                int32_t c = plist[j];
                if (!shas[c]) {         /* (cannot happen: see gi.bounded.class_plan) */
                    Py_DECREF(plan);
                    plan = Py_NotImplemented;
                    Py_INCREF(plan);
                    goto done;
                }
                if (bestc < 0) {
                    bestc = c;
                    continue;
                }
                if (sbig3[c] != sbig3[bestc]) { if (sbig3[c] < sbig3[bestc]) bestc = c; continue; }
                if (srisk[c] != srisk[bestc]) { if (srisk[c] < srisk[bestc]) bestc = c; continue; }
                if (spairs[c] != spairs[bestc]) { if (spairs[c] < spairs[bestc]) bestc = c; continue; }
                if (near[c] != near[bestc]) { if (near[c] > near[bestc]) bestc = c; continue; }
                if (c < bestc)
                    bestc = c;
            }
            if (sbig3[bestc]) {         /* BFS instead */
                Py_DECREF(plan);
                plan = Py_None;
                Py_INCREF(plan);
                goto done;
            }
            layer[0] = bestc;
            nlayer = 1;
        }
        lay = PyList_New(nlayer);
        if (lay == NULL) {
            Py_CLEAR(plan);
            goto done;
        }
        for (j = 0; j < nlayer; j++)
            PyList_SET_ITEM(lay, j, int_ref(layer[j]));
        k = PyList_Append(plan, lay);
        Py_DECREF(lay);
        if (k < 0) {
            Py_CLEAR(plan);
            goto done;
        }
        for (j = 0; j < nlayer; j++) {
            int32_t c = layer[j], t, last;
            pend[c] = 0;
            last = plist[--npend];
            t = pidx[c];
            plist[t] = last;
            pidx[last] = t;
            shas[c] = 0;
            for (t = mstart[c]; t < mstart[c + 1]; t++)
                done[memb[t]] = 1;
        }
        if (npend > 0)
            for (j = 0; j < nlayer; j++) {
                int32_t c = layer[j], t;
                for (t = mstart[c]; t < mstart[c + 1]; t++)
                    PLACED(memb[t]);
            }
    }
#undef PLACED
done:
    free(off); free(adj); free(col); free(mstart); free(memb); free(plist); free(pidx);
    free(upbuf); free(uplen); free(upstart); free(idx); free(itmp); free(dlist); free(dets);
    free(spairs); free(layer); free(near); free(done); free(pend); free(dirty); free(shas);
    free(sbig3); free(srisk); free(det);
    return plan;
}

/* Bit-parallel balls (gi.bounded._truncated_profiles). A capsule holding the
 * bitsets; balls_step advances one round, returning the sphere sizes (a list
 * of ints, or of tuples of per-color counts) or None once the balls stop
 * growing. balls_new(nbr, colidx, ncolors): colidx (a list of color indices in
 * [0, ncolors) when the profile is colored; None otherwise). */
typedef struct {
    Py_ssize_t n, W, ncol, m;
    int32_t *off, *adj;
    uint64_t *cur, *nxt, *cmask;
} balls_t;

static void balls_free(PyObject *cap)
{
    balls_t *b = PyCapsule_GetPointer(cap, "gi.balls");
    if (b) {
        free(b->off); free(b->adj); free(b->cur); free(b->nxt); free(b->cmask);
        free(b);
    }
}

static PyObject *ck_balls_new(PyObject *m_, PyObject *const *args, Py_ssize_t nargs)
{
    balls_t *b;
    PyObject *cap;
    Py_ssize_t n, W, v, ncol = 0;
    int32_t *colidx = NULL;
    int ok;
    (void)m_;
    if (nargs != 3 || !PyList_CheckExact(args[0]))
        Py_RETURN_NONE;
    n = PyList_GET_SIZE(args[0]);
    if (n == 0)
        Py_RETURN_NONE;
    W = (n + 63) / 64;
    if ((size_t)n > SIZE_MAX / 16 / (size_t)W)
        Py_RETURN_NONE;
    if (args[1] != Py_None) {
        if (!read_small(args[2], &ncol) || ncol < 1 || ncol > 64)
            Py_RETURN_NONE;
        colidx = malloc((size_t)n * sizeof(int32_t));
        if (colidx == NULL)
            return PyErr_NoMemory();
        if (!read_ints(args[1], n, colidx)) {
            free(colidx);
            Py_RETURN_NONE;
        }
        for (v = 0; v < n; v++)
            if (colidx[v] < 0 || colidx[v] >= ncol) {
                free(colidx);
                Py_RETURN_NONE;
            }
    }
    b = calloc(1, sizeof(balls_t));
    if (b == NULL) {
        free(colidx);
        return PyErr_NoMemory();
    }
    b->n = n; b->W = W; b->ncol = ncol;
    ok = read_adj(args[0], n, 0, &b->off, &b->adj);
    if (ok <= 0) {
        free(colidx);
        free(b);
        if (ok < 0)
            return NULL;
        Py_RETURN_NONE;
    }
    b->m = b->off[n];
    b->cur = calloc((size_t)n * (size_t)W, sizeof(uint64_t));
    b->nxt = calloc((size_t)n * (size_t)W, sizeof(uint64_t));
    if (ncol)
        b->cmask = calloc((size_t)ncol * (size_t)W, sizeof(uint64_t));
    if (!b->cur || !b->nxt || (ncol && !b->cmask)) {
        free(colidx);
        free(b->off); free(b->adj); free(b->cur); free(b->nxt); free(b->cmask); free(b);
        return PyErr_NoMemory();
    }
    for (v = 0; v < n; v++)
        b->cur[v * W + v / 64] = (uint64_t)1 << (v % 64);
    if (ncol)
        for (v = 0; v < n; v++)
            b->cmask[colidx[v] * W + v / 64] |= (uint64_t)1 << (v % 64);
    free(colidx);
    cap = PyCapsule_New(b, "gi.balls", balls_free);
    if (cap == NULL) {
        free(b->off); free(b->adj); free(b->cur); free(b->nxt); free(b->cmask); free(b);
    }
    return cap;
}

static PyObject *ck_balls_step(PyObject *m_, PyObject *const *args, Py_ssize_t nargs)
{
    balls_t *b;
    Py_ssize_t n, W, v, j, w, c;
    uint64_t *cur, *nxt;
    PyObject *out;
    int changed = 0, ok;
    (void)m_;
    if (nargs != 1 || !PyCapsule_IsValid(args[0], "gi.balls")) {
        PyErr_SetString(PyExc_TypeError, "balls_step(capsule)");
        return NULL;
    }
    b = PyCapsule_GetPointer(args[0], "gi.balls");
    if (b == NULL)
        return NULL;
    n = b->n; W = b->W;
    cur = b->cur; nxt = b->nxt;
    for (v = 0; v < n; v++) {
        uint64_t *dst = nxt + v * W;
        memcpy(dst, cur + v * W, (size_t)W * sizeof(uint64_t));
        for (j = b->off[v]; j < b->off[v + 1]; j++) {
            const uint64_t *src = cur + (Py_ssize_t)b->adj[j] * W;
            for (w = 0; w < W; w++)
                dst[w] |= src[w];
        }
        if (!changed && memcmp(dst, cur + v * W, (size_t)W * sizeof(uint64_t)) != 0)
            changed = 1;
    }
    if (!changed)
        Py_RETURN_NONE;
    ok = ints_ensure(n + 1);
    if (ok < 0)
        return NULL;
    if (ok == 0) {
        PyErr_SetString(PyExc_ValueError, "balls_step: graph too large");
        return NULL;
    }
    out = PyList_New(n);
    if (out == NULL)
        return NULL;
    for (v = 0; v < n; v++) {
        uint64_t *cv = cur + v * W, *nv = nxt + v * W;
        PyObject *o;
        if (b->ncol == 0) {
            Py_ssize_t cnt = 0;
            for (w = 0; w < W; w++)
                cnt += __builtin_popcountll(cv[w] ^ nv[w]);
            o = int_ref(cnt);
        } else {
            o = PyTuple_New(b->ncol);
            if (o == NULL) {
                Py_DECREF(out);
                return NULL;
            }
            for (c = 0; c < b->ncol; c++) {
                Py_ssize_t cnt = 0;
                const uint64_t *mk = b->cmask + c * W;
                for (w = 0; w < W; w++)
                    cnt += __builtin_popcountll((cv[w] ^ nv[w]) & mk[w]);
                PyTuple_SET_ITEM(o, c, int_ref(cnt));
            }
        }
        PyList_SET_ITEM(out, v, o);
    }
    b->cur = nxt;                       /* the balls advance */
    b->nxt = cur;
    return out;
}

/* Edge-orbit bookkeeping for gi.canon.canon_connected: a capsule with the
 * sorted adjacency (off, adj: edge (u, adj[j]) has index j in canon_connected's
 * enumeration of the oriented edges), the candidate edges (eu, ev) and the map
 * e2k[e] = position of edge e among the candidates or -1. */
typedef struct {
    Py_ssize_t n, m, k;
    int32_t *off, *adj, *eu, *ev, *e2k;
} orbtab_t;

static void orbtab_free(PyObject *cap)
{
    orbtab_t *t = PyCapsule_GetPointer(cap, "gi.orbtab");
    if (t) {
        free(t->off); free(t->adj); free(t->eu); free(t->ev); free(t->e2k);
        free(t);
    }
}

/* orbit_table(nbr, cand): cand is the list of edge indices of the candidate
 * edges (indices into the enumeration of oriented edges, u increasing, then
 * position in nbr[u]). */
static PyObject *ck_orbit_table(PyObject *m_, PyObject *const *args, Py_ssize_t nargs)
{
    orbtab_t *t;
    PyObject *cand, *cap;
    Py_ssize_t n, k, i, f;
    int ok;
    (void)m_;
    if (nargs != 2 || !PyList_CheckExact(args[0]) || !PyList_CheckExact(args[1]))
        Py_RETURN_NONE;
    n = PyList_GET_SIZE(args[0]);
    if (n == 0 || n >= INT32_MAX)
        Py_RETURN_NONE;
    cand = args[1];
    k = PyList_GET_SIZE(cand);
    t = calloc(1, sizeof(orbtab_t));
    if (t == NULL)
        return PyErr_NoMemory();
    t->n = n; t->k = k;
    ok = read_adj(args[0], n, 1, &t->off, &t->adj);
    if (ok <= 0) {
        free(t);
        if (ok < 0)
            return NULL;
        Py_RETURN_NONE;
    }
    t->m = t->off[n];
    t->eu = malloc((size_t)(k ? k : 1) * sizeof(int32_t));
    t->ev = malloc((size_t)(k ? k : 1) * sizeof(int32_t));
    t->e2k = malloc((size_t)(t->m ? t->m : 1) * sizeof(int32_t));
    if (!t->eu || !t->ev || !t->e2k) {
        free(t->off); free(t->adj); free(t->eu); free(t->ev); free(t->e2k); free(t);
        return PyErr_NoMemory();
    }
    memset(t->e2k, 0xff, (size_t)(t->m ? t->m : 1) * sizeof(int32_t));
    {
        /* the source vertex of each edge index */
        int32_t *owner = malloc((size_t)(t->m ? t->m : 1) * sizeof(int32_t));
        Py_ssize_t v;
        if (owner == NULL) {
            free(t->off); free(t->adj); free(t->eu); free(t->ev); free(t->e2k); free(t);
            return PyErr_NoMemory();
        }
        for (v = 0; v < n; v++) {
            Py_ssize_t j;
            for (j = t->off[v]; j < t->off[v + 1]; j++)
                owner[j] = (int32_t)v;
        }
        for (i = 0; i < k; i++) {
            if (!read_index(PyList_GET_ITEM(cand, i), t->m, &f) || t->e2k[f] != -1) {
                free(owner);
                free(t->off); free(t->adj); free(t->eu); free(t->ev); free(t->e2k); free(t);
                Py_RETURN_NONE;
            }
            t->e2k[f] = (int32_t)i;
            t->eu[i] = owner[f];
            t->ev[i] = t->adj[f];
        }
        free(owner);
    }
    cap = PyCapsule_New(t, "gi.orbtab", orbtab_free);
    if (cap == NULL) {
        free(t->off); free(t->adj); free(t->eu); free(t->ev); free(t->e2k); free(t);
    }
    return cap;
}

static inline int32_t uf_find(int32_t *p, int32_t x)
{
    int32_t r = x;
    while (p[r] != r)
        r = p[r];
    while (p[x] != r) {
        int32_t y = p[x];
        p[x] = r;
        x = y;
    }
    return r;
}

/* orbit_absorb(table, parent, comps, a): the absorb of canon_connected for the
 * automorphism a (a tuple on range(n)): for each candidate edge (u, v) union
 * its class with that of (a[u], a[v]). parent (a list, parent[i] <= i) is the
 * union-find forest shared with the Python find; roots are the least members
 * of their classes as in the reference, so it remains valid for both. Returns
 * the number of merges, or None (nothing changed) on unusual input, including
 * an image outside the candidates (the reference then raises). */
static PyObject *ck_orbit_absorb(PyObject *m_, PyObject *const *args, Py_ssize_t nargs)
{
    orbtab_t *t;
    PyObject *parent, *a;
    Py_ssize_t k, i, comps, merges = 0;
    int32_t *img = NULL, *ga = NULL, *p = NULL, *p0 = NULL;
    PyObject *res = NULL;
    (void)m_;
    if (nargs != 4 || !PyCapsule_IsValid(args[0], "gi.orbtab"))
        Py_RETURN_NONE;
    t = PyCapsule_GetPointer(args[0], "gi.orbtab");
    if (t == NULL)
        return NULL;
    parent = args[1];
    a = args[3];
    k = t->k;
    if (!PyList_CheckExact(parent) || PyList_GET_SIZE(parent) != k
        || !read_small(args[2], &comps)
        || !PyTuple_CheckExact(a) || PyTuple_GET_SIZE(a) != t->n)
        Py_RETURN_NONE;
    if (ints_ensure(k + 1) != 1) {
        if (PyErr_Occurred())
            return NULL;
        Py_RETURN_NONE;
    }
    img = malloc((size_t)(k ? k : 1) * sizeof(int32_t));
    ga = malloc((size_t)t->n * sizeof(int32_t));
    p = malloc((size_t)(k ? k : 1) * sizeof(int32_t));
    p0 = malloc((size_t)(k ? k : 1) * sizeof(int32_t));
    if (!img || !ga || !p || !p0) {
        PyErr_NoMemory();
        goto done;
    }
    for (i = 0; i < t->n; i++) {
        Py_ssize_t v;
        if (!read_index(PyTuple_GET_ITEM(a, i), t->n, &v))
            goto use_python;
        ga[i] = (int32_t)v;
    }
    for (i = 0; i < k; i++) {
        Py_ssize_t v;
        if (!read_index(PyList_GET_ITEM(parent, i), k, &v) || v > i)
            goto use_python;
        p[i] = (int32_t)v;
        p0[i] = (int32_t)v;
    }
    for (i = 0; i < k; i++) {
        int32_t x = ga[t->eu[i]], y = ga[t->ev[i]];
        int32_t lo = t->off[x], hi = t->off[x + 1] - 1, f = -1;
        while (lo <= hi) {
            int32_t mid = lo + (hi - lo) / 2;
            if (t->adj[mid] == y) {
                f = mid;
                break;
            }
            if (t->adj[mid] < y)
                lo = mid + 1;
            else
                hi = mid - 1;
        }
        if (f < 0 || t->e2k[f] < 0)
            goto use_python;
        img[i] = t->e2k[f];
    }
    for (i = 0; i < k && comps - merges > 1; i++) {
        int32_t r1 = uf_find(p, (int32_t)i), r2 = uf_find(p, img[i]);
        if (r1 != r2) {
            if (r1 < r2)
                p[r2] = r1;
            else
                p[r1] = r2;
            merges++;
        }
    }
    for (i = 0; i < k; i++)
        if (p[i] != p0[i]) {
            PyObject *o = int_ref(p[i]);
            if (PyList_SetItem(parent, i, o) < 0)
                goto done;
        }
    res = PyLong_FromSsize_t(merges);
    goto done;
use_python:
    res = Py_None;
    Py_INCREF(res);
done:
    free(img); free(ga); free(p); free(p0);
    return res;
}
/* ===== end of w23-speed2 block ===== */

/* Closure of positions under dense permutations (gi.canon.step, dense path).
 * closure_dense(seeds, gens, kind) -> (pos, acts) or None.
 * seeds: a list of frozensets (kind 0) or of pairs of ints (kind 1), the
 * positions; gens: a list of permutations (tuples of exact ints). pos: the
 * closure of seeds under gens, sorted by sorted label tuple (kind 0) or by pair
 * (kind 1), with the given objects for the seeds and new ones (frozensets or
 * tuples) for the images; acts: for each generator the tuple of the indices of
 * the images of the positions of pos. Same output as the Python closure then
 * sorted(...). Sets are read as sorted int arrays and compared by content. */
typedef struct {
    int32_t *data;      /* the sets, concatenated */
    int32_t *off;       /* off[i]: start of set i; off[size] the end */
    Py_ssize_t size, cap, dcap;
    int32_t *table;     /* open addressing: -1 or the index of a set */
    Py_ssize_t tmask;
} setstore_t;

static uint64_t set_hash(const int32_t *s, Py_ssize_t len)
{
    uint64_t h = 0xcbf29ce484222325ULL ^ (uint64_t)len;
    Py_ssize_t i;
    for (i = 0; i < len; i++) {
        h ^= (uint32_t)s[i];
        h *= 0x100000001b3ULL;
    }
    h ^= h >> 29;
    return h;
}

static int store_init(setstore_t *st, Py_ssize_t cap)
{
    st->size = 0;
    st->cap = cap < 16 ? 16 : cap;
    st->dcap = st->cap * 4;
    st->data = malloc((size_t)st->dcap * sizeof(int32_t));
    st->off = malloc((size_t)(st->cap + 1) * sizeof(int32_t));
    st->tmask = 63;
    while (st->tmask + 1 < st->cap * 2)
        st->tmask = st->tmask * 2 + 1;
    st->table = malloc((size_t)(st->tmask + 1) * sizeof(int32_t));
    if (!st->data || !st->off || !st->table)
        return 0;
    memset(st->table, 0xff, (size_t)(st->tmask + 1) * sizeof(int32_t));
    st->off[0] = 0;
    return 1;
}

static void store_free(setstore_t *st)
{
    free(st->data); free(st->off); free(st->table);
}

/* The index of the set s (sorted, len), inserted if new (*isnew = 1). -1 on
 * memory exhaustion. */
static Py_ssize_t store_find(setstore_t *st, const int32_t *s, Py_ssize_t len, int *isnew)
{
    uint64_t h = set_hash(s, len);
    Py_ssize_t i = (Py_ssize_t)(h & (uint64_t)st->tmask);
    *isnew = 0;
    for (;;) {
        int32_t e = st->table[i];
        if (e < 0)
            break;
        if (st->off[e + 1] - st->off[e] == len
            && memcmp(st->data + st->off[e], s, (size_t)len * sizeof(int32_t)) == 0)
            return e;
        i = (i + 1) & st->tmask;
    }
    if (st->size == st->cap || st->off[st->size] + len > st->dcap) {
        if (st->size == st->cap) {
            Py_ssize_t ncap = st->cap * 2;
            int32_t *no = realloc(st->off, (size_t)(ncap + 1) * sizeof(int32_t));
            if (!no)
                return -1;
            st->off = no;
            st->cap = ncap;
        }
        while (st->off[st->size] + len > st->dcap) {
            Py_ssize_t ndcap = st->dcap * 2;
            int32_t *nd = realloc(st->data, (size_t)ndcap * sizeof(int32_t));
            if (!nd)
                return -1;
            st->data = nd;
            st->dcap = ndcap;
        }
    }
    memcpy(st->data + st->off[st->size], s, (size_t)len * sizeof(int32_t));
    st->off[st->size + 1] = st->off[st->size] + (int32_t)len;
    st->table[i] = (int32_t)st->size;
    st->size++;
    *isnew = 1;
    if (st->size * 2 > st->tmask) {     /* grow the table */
        Py_ssize_t nmask = st->tmask * 2 + 1, k;
        int32_t *nt = malloc((size_t)(nmask + 1) * sizeof(int32_t));
        if (!nt)
            return -1;
        memset(nt, 0xff, (size_t)(nmask + 1) * sizeof(int32_t));
        for (k = 0; k < st->size; k++) {
            uint64_t hh = set_hash(st->data + st->off[k], st->off[k + 1] - st->off[k]);
            Py_ssize_t j = (Py_ssize_t)(hh & (uint64_t)nmask);
            while (nt[j] >= 0)
                j = (j + 1) & nmask;
            nt[j] = (int32_t)k;
        }
        free(st->table);
        st->table = nt;
        st->tmask = nmask;
    }
    return st->size - 1;
}

/* Sorts m ints ascending (insertion sort; for long arrays a merge sort using
 * the scratch space *sp of capacity *capp, grown as needed; *capp = -1 reports
 * memory exhaustion). */
static void sort_i32(int32_t *a, Py_ssize_t m, int32_t **sp, Py_ssize_t *capp)
{
    Py_ssize_t i, j;
    if (m < 48) {
        for (i = 1; i < m; i++) {
            int32_t x = a[i];
            for (j = i; j > 0 && a[j - 1] > x; j--)
                a[j] = a[j - 1];
            a[j] = x;
        }
        return;
    }
    if (*capp < m) {
        int32_t *t = realloc(*sp, (size_t)m * sizeof(int32_t));
        if (!t) {
            *capp = -1;
            return;
        }
        *sp = t;
        *capp = m;
    }
    {
        int32_t *src = a, *dst = *sp, *t;
        Py_ssize_t w, lo, mid, hi, k;
        for (w = 1; w < m; w *= 2) {
            for (lo = 0; lo < m; lo += 2 * w) {
                mid = lo + w < m ? lo + w : m;
                hi = lo + 2 * w < m ? lo + 2 * w : m;
                i = lo; j = mid; k = lo;
                while (i < mid && j < hi)
                    dst[k++] = src[j] < src[i] ? src[j++] : src[i++];
                while (i < mid)
                    dst[k++] = src[i++];
                while (j < hi)
                    dst[k++] = src[j++];
            }
            t = src; src = dst; dst = t;
        }
        if (src != a)
            memcpy(a, src, (size_t)m * sizeof(int32_t));
    }
}

static inline int set_lt(const setstore_t *st, int32_t a, int32_t b)
{
    Py_ssize_t la = st->off[a + 1] - st->off[a], lb = st->off[b + 1] - st->off[b], k;
    const int32_t *x = st->data + st->off[a], *y = st->data + st->off[b];
    for (k = 0; k < la && k < lb; k++)
        if (x[k] != y[k])
            return x[k] < y[k];
    return la < lb;
}

static void sort_sets(int32_t *idx, int32_t *tmp, Py_ssize_t s, const setstore_t *st)
{
    Py_ssize_t w, i, j, k, lo, mid, hi;
    int32_t *src = idx, *dst = tmp, *t;
    for (w = 1; w < s; w *= 2) {
        for (lo = 0; lo < s; lo += 2 * w) {
            mid = lo + w < s ? lo + w : s;
            hi = lo + 2 * w < s ? lo + 2 * w : s;
            i = lo;
            j = mid;
            k = lo;
            while (i < mid && j < hi) {
                if (set_lt(st, src[j], src[i]))
                    dst[k++] = src[j++];
                else
                    dst[k++] = src[i++];
            }
            while (i < mid)
                dst[k++] = src[i++];
            while (j < hi)
                dst[k++] = src[j++];
        }
        t = src; src = dst; dst = t;
    }
    if (src != idx)
        memcpy(idx, src, (size_t)s * sizeof(int32_t));
}

static PyObject *ck_closure_dense(PyObject *m_, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *seeds, *gensobj, *res = NULL, *pos = NULL, *acts = NULL;
    Py_ssize_t ns, ng, n = 0, i, g, kind;
    int32_t *flat = NULL, *imgbuf = NULL, *order = NULL, *rank_ = NULL, *itmp = NULL;
    int32_t **rows = NULL;
    Py_ssize_t rowcap = 0;
    PyObject **seedobj = NULL;
    setstore_t st;
    int st_ok = 0;
    Py_ssize_t maxlen = 0, sortcap = 0;
    int32_t *sortscratch = NULL;
    (void)m_;
    memset(&st, 0, sizeof(st));
    if (nargs != 3 || !PyList_CheckExact(args[0]) || !PyList_CheckExact(args[1])
        || !read_small(args[2], &kind) || (kind != 0 && kind != 1))
        Py_RETURN_NONE;
    seeds = args[0];
    gensobj = args[1];
    ns = PyList_GET_SIZE(seeds);
    ng = PyList_GET_SIZE(gensobj);
    if (ng == 0)
        Py_RETURN_NONE;
    {
        PyObject *g0 = PyList_GET_ITEM(gensobj, 0);
        if (!PyTuple_CheckExact(g0))
            Py_RETURN_NONE;
        n = PyTuple_GET_SIZE(g0);
    }
    if (n == 0 || (size_t)ng > SIZE_MAX / sizeof(int32_t) / (size_t)n)
        Py_RETURN_NONE;
    if (ints_ensure(n) != 1) {
        if (PyErr_Occurred())
            return NULL;
        Py_RETURN_NONE;
    }
    flat = malloc((size_t)(ng * n) * sizeof(int32_t));
    seedobj = malloc((size_t)(ns ? ns : 1) * sizeof(PyObject *));
    rows = calloc((size_t)ng, sizeof(int32_t *));
    if (!flat || !seedobj || !rows) {
        PyErr_NoMemory();
        goto done;
    }
    for (g = 0; g < ng; g++) {
        PyObject *gt = PyList_GET_ITEM(gensobj, g);
        if (!PyTuple_CheckExact(gt) || PyTuple_GET_SIZE(gt) != n)
            goto use_python;
        for (i = 0; i < n; i++) {
            Py_ssize_t v;
            if (!read_index(PyTuple_GET_ITEM(gt, i), n, &v))
                goto use_python;
            flat[g * n + i] = (int32_t)v;
        }
    }
    if (!store_init(&st, ns * 2 + 16)) {
        PyErr_NoMemory();
        goto done;
    }
    st_ok = 1;
    /* the seeds */
    {
        Py_ssize_t cap = 64;
        int32_t *buf = malloc((size_t)cap * sizeof(int32_t));
        if (!buf) {
            PyErr_NoMemory();
            goto done;
        }
        for (i = 0; i < ns; i++) {
            PyObject *s = PyList_GET_ITEM(seeds, i);
            Py_ssize_t len = 0, idx;
            int isnew;
            if (kind == 0) {
                PyObject *key;
                Py_ssize_t pos2 = 0;
                Py_hash_t h;
                if (!PyFrozenSet_CheckExact(s)) {
                    free(buf);
                    goto use_python;
                }
                len = PySet_GET_SIZE(s);
                if (len > cap) {
                    int32_t *nb;
                    cap = len * 2;
                    nb = realloc(buf, (size_t)cap * sizeof(int32_t));
                    if (!nb) {
                        free(buf);
                        PyErr_NoMemory();
                        goto done;
                    }
                    buf = nb;
                }
                len = 0;
#if PY_VERSION_HEX < 0x030D0000
                while (_PySet_NextEntry(s, &pos2, &key, &h)) {
#else
                {
                    PyObject *it = PyObject_GetIter(s);
                    if (it == NULL) {
                        free(buf);
                        goto done;
                    }
                    (void)pos2; (void)h;
                    while ((key = PyIter_Next(it)) != NULL) {
                        Py_DECREF(key);         /* (the set holds a reference) */
#endif
                    Py_ssize_t v;
                    if (!read_index(key, n, &v)) {
#if PY_VERSION_HEX >= 0x030D0000
                        Py_DECREF(it);
#endif
                        free(buf);
                        goto use_python;
                    }
                    buf[len++] = (int32_t)v;
                }
#if PY_VERSION_HEX >= 0x030D0000
                    Py_DECREF(it);
                    if (PyErr_Occurred()) {
                        free(buf);
                        goto done;
                    }
                }
#endif
                sort_i32(buf, len, &sortscratch, &sortcap);
                if (sortcap < 0) {
                    free(buf);
                    PyErr_NoMemory();
                    goto done;
                }
            } else {
                Py_ssize_t a, b;
                if (!PyTuple_CheckExact(s) || PyTuple_GET_SIZE(s) != 2
                    || !read_index(PyTuple_GET_ITEM(s, 0), n, &a)
                    || !read_index(PyTuple_GET_ITEM(s, 1), n, &b) || a >= b) {
                    free(buf);
                    goto use_python;
                }
                buf[0] = (int32_t)a;
                buf[1] = (int32_t)b;
                len = 2;
            }
            if (len > maxlen)
                maxlen = len;
            idx = store_find(&st, buf, len, &isnew);
            if (idx < 0) {
                free(buf);
                PyErr_NoMemory();
                goto done;
            }
            if (!isnew || idx != i) {   /* (a repeated seed: the reference's dedup
                                           by a dict never produced this) */
                free(buf);
                goto use_python;
            }
            seedobj[i] = s;
        }
        free(buf);
    }
    imgbuf = malloc((size_t)(maxlen ? maxlen : 1) * sizeof(int32_t));
    if (!imgbuf) {
        PyErr_NoMemory();
        goto done;
    }
    rowcap = st.size * 2 + 16;
    for (g = 0; g < ng; g++) {
        rows[g] = malloc((size_t)rowcap * sizeof(int32_t));
        if (!rows[g]) {
            PyErr_NoMemory();
            goto done;
        }
    }
    for (i = 0; i < st.size; i++) {     /* (the store grows: a BFS over the orbits) */
        Py_ssize_t len = st.off[i + 1] - st.off[i], k;
        if (i == rowcap) {
            rowcap *= 2;
            for (g = 0; g < ng; g++) {
                int32_t *nr = realloc(rows[g], (size_t)rowcap * sizeof(int32_t));
                if (!nr) {
                    PyErr_NoMemory();
                    goto done;
                }
                rows[g] = nr;
            }
        }
        if ((i & 0x3ff) == 0x3ff && PyErr_CheckSignals() < 0)
            goto done;
        for (g = 0; g < ng; g++) {
            const int32_t *im = flat + g * n;
            Py_ssize_t idx;
            int isnew;
            for (k = 0; k < len; k++)
                imgbuf[k] = im[st.data[st.off[i] + k]];
            sort_i32(imgbuf, len, &sortscratch, &sortcap);
            if (sortcap < 0) {
                PyErr_NoMemory();
                goto done;
            }
            idx = store_find(&st, imgbuf, len, &isnew);
            if (idx < 0) {
                PyErr_NoMemory();
                goto done;
            }
            rows[g][i] = (int32_t)idx;
        }
    }
    /* sort the closure by content */
    order = malloc((size_t)st.size * sizeof(int32_t));
    rank_ = malloc((size_t)st.size * sizeof(int32_t));
    itmp = malloc((size_t)st.size * sizeof(int32_t));
    if (!order || !rank_ || !itmp) {
        PyErr_NoMemory();
        goto done;
    }
    for (i = 0; i < st.size; i++)
        order[i] = (int32_t)i;
    sort_sets(order, itmp, st.size, &st);
    for (i = 0; i < st.size; i++)
        rank_[order[i]] = (int32_t)i;
    pos = PyList_New(st.size);
    acts = PyList_New(ng);
    if (!pos || !acts)
        goto done;
    if (ints_ensure(st.size) < 0)
        goto done;
    for (i = 0; i < st.size; i++) {
        int32_t o = order[i];
        PyObject *obj;
        if (o < ns) {
            obj = seedobj[o];
            Py_INCREF(obj);
        } else {
            Py_ssize_t len = st.off[o + 1] - st.off[o], k;
            PyObject *t = PyTuple_New(len);
            if (!t)
                goto done;
            for (k = 0; k < len; k++)
                PyTuple_SET_ITEM(t, k, int_ref(st.data[st.off[o] + k]));
            if (kind == 0) {
                obj = PyFrozenSet_New(t);
                Py_DECREF(t);
                if (!obj)
                    goto done;
            } else {
                obj = t;
            }
        }
        PyList_SET_ITEM(pos, i, obj);
    }
    for (g = 0; g < ng; g++) {
        PyObject *t = PyTuple_New(st.size);
        if (!t)
            goto done;
        for (i = 0; i < st.size; i++) {
            int32_t o = order[i];
            PyTuple_SET_ITEM(t, i, int_ref(rank_[rows[g][o]]));
        }
        PyList_SET_ITEM(acts, g, t);
    }
    res = PyTuple_Pack(2, pos, acts);
    goto done;
use_python:
    res = Py_None;
    Py_INCREF(res);
done:
    if (st_ok)
        store_free(&st);
    if (rows) {
        for (g = 0; g < ng; g++)
            free(rows[g]);
        free(rows);
    }
    free(flat); free(seedobj); free(imgbuf); free(order); free(rank_); free(itmp);
    free(sortscratch);
    Py_XDECREF(pos);
    Py_XDECREF(acts);
    return res;
}
/* ===== end of w23-speed2 block (2) ===== */

/* Iterating a set of exact small non-negative ints. A helper that appends the
 * entries of the set s to *pbuf (ints) and, if objs is given, their objects.
 * Returns the number appended, or -1 if s is unusual (not a set of exact small
 * ints; nothing appended); memory errors set *nomem = 1. */
static Py_ssize_t set_ints(PyObject *s, int32_t **pbuf, Py_ssize_t *pcap, Py_ssize_t len0,
                           PyObject ***pobj, int *nomem)
{
    Py_ssize_t size = PySet_GET_SIZE(s), v, app = 0;
    if (len0 + size > *pcap) {
        Py_ssize_t nc = (len0 + size) * 2 + 16;
        int32_t *nb = realloc(*pbuf, (size_t)nc * sizeof(int32_t));
        if (!nb) { *nomem = 1; return -1; }
        *pbuf = nb;
        if (pobj != NULL) {
            PyObject **no = realloc(*pobj, (size_t)nc * sizeof(PyObject *));
            if (!no) { *nomem = 1; return -1; }
            *pobj = no;
        }
        *pcap = nc;
    }
#if PY_VERSION_HEX < 0x030D0000
    {
        Py_ssize_t pos = 0;
        Py_hash_t h;
        PyObject *key;
        while (_PySet_NextEntry(s, &pos, &key, &h)) {
            if (!read_small(key, &v) || v < 0)
                return -1;
            (*pbuf)[len0 + app] = (int32_t)v;
            if (pobj != NULL)
                (*pobj)[len0 + app] = key;
            app++;
        }
    }
#else
    {
        PyObject *it = PyObject_GetIter(s), *key;
        if (it == NULL) {
            PyErr_Clear();
            return -1;
        }
        while ((key = PyIter_Next(it)) != NULL) {
            Py_DECREF(key);             /* (the set holds a reference) */
            if (!read_small(key, &v) || v < 0) {
                Py_DECREF(it);
                return -1;
            }
            (*pbuf)[len0 + app] = (int32_t)v;
            if (pobj != NULL)
                (*pobj)[len0 + app] = key;
            app++;
        }
        Py_DECREF(it);
        if (PyErr_Occurred()) {
            PyErr_Clear();
            return -1;
        }
    }
#endif
    return app;
}

/* The int object of the label v (borrowed); NULL with an exception. */
static inline PyObject *label_obj(Py_ssize_t v)
{
    if (v >= ints_cap && ints_ensure(v + 1) < 0)
        return NULL;
    if (v >= ints_cap) {                /* above the table's maximum */
        PyErr_SetString(PyExc_MemoryError, "_ckernel: label too large");
        return NULL;
    }
    return ints_tab[v];
}

/* Closure of positions under a SparseEA (gi.canon._closure_sparse, plus the
 * sort of the positions and the move of the table to their indices).
 * closure_sparse(seeds, gens, who, kind) -> (pos, table) or None.
 * seeds: frozensets (kind 0) or int pairs (kind 1); gens: the dict {id: {moved
 * point: image}}; who: {point: set of ids}. pos: the closure sorted (see
 * closure_dense); table: {id: {index of a position it moves: index of its
 * image}} for every generator moving a point of some position (possibly an
 * empty dict). */
static PyObject *ck_closure_sparse(PyObject *m_, PyObject *const *args, Py_ssize_t nargs)
{
    PyObject *seeds, *gens, *who, *res = NULL, *pos = NULL, *table = NULL;
    Py_ssize_t ns, i, kind, maxlab = 0, trip_n = 0, trip_cap = 0, ids_cap = 0, sortcap = 0;
    int32_t *imgbuf = NULL, *idsbuf = NULL, *order = NULL, *rank_ = NULL, *itmp = NULL, *trip = NULL;
    int32_t *sortscratch = NULL;
    PyObject **seedobj = NULL, **idobj = NULL, **uobj = NULL;
    uint64_t *idkeys = NULL, *idkeytmp = NULL;
    Py_ssize_t imgcap = 0, keycap = 0, uobjcap = 0;
    setstore_t st;
    int st_ok = 0, nomem = 0;
    (void)m_;
    memset(&st, 0, sizeof(st));
    if (nargs != 4 || !PyList_CheckExact(args[0]) || !PyDict_CheckExact(args[1])
        || !PyDict_CheckExact(args[2]) || !read_small(args[3], &kind)
        || (kind != 0 && kind != 1))
        Py_RETURN_NONE;
    seeds = args[0];
    gens = args[1];
    who = args[2];
    ns = PyList_GET_SIZE(seeds);
    seedobj = malloc((size_t)(ns ? ns : 1) * sizeof(PyObject *));
    if (!seedobj) {
        PyErr_NoMemory();
        goto done;
    }
    if (!store_init(&st, ns * 2 + 16)) {
        PyErr_NoMemory();
        goto done;
    }
    st_ok = 1;
    for (i = 0; i < ns; i++) {
        PyObject *s = PyList_GET_ITEM(seeds, i);
        Py_ssize_t len, idx;
        int isnew;
        if (kind == 0) {
            if (!PyFrozenSet_CheckExact(s))
                goto use_python;
            len = set_ints(s, &imgbuf, &imgcap, 0, NULL, &nomem);
            if (len < 0) {
                if (nomem) { PyErr_NoMemory(); goto done; }
                goto use_python;
            }
            sort_i32(imgbuf, len, &sortscratch, &sortcap);
        } else {
            Py_ssize_t a, b;
            if (imgcap < 2) {
                int32_t *nb = realloc(imgbuf, 16 * sizeof(int32_t));
                if (!nb) { PyErr_NoMemory(); goto done; }
                imgbuf = nb;
                imgcap = 16;
            }
            if (!PyTuple_CheckExact(s) || PyTuple_GET_SIZE(s) != 2
                || !read_small(PyTuple_GET_ITEM(s, 0), &a) || a < 0
                || !read_small(PyTuple_GET_ITEM(s, 1), &b) || b <= a)
                goto use_python;
            imgbuf[0] = (int32_t)a;
            imgbuf[1] = (int32_t)b;
            len = 2;
        }
        if (sortcap < 0) { PyErr_NoMemory(); goto done; }
        {
            Py_ssize_t q;
            for (q = 0; q < len; q++)
                if (imgbuf[q] > maxlab)
                    maxlab = imgbuf[q];
        }
        idx = store_find(&st, imgbuf, len, &isnew);
        if (idx < 0) { PyErr_NoMemory(); goto done; }
        if (!isnew || idx != i)
            goto use_python;
        seedobj[i] = s;
    }
    if (ints_ensure(maxlab + 1) < 0)
        goto done;
    for (i = 0; i < st.size; i++) {     /* (the store grows: a BFS) */
        Py_ssize_t len = st.off[i + 1] - st.off[i], k, nids = 0, q;
        if (len > imgcap) {
            Py_ssize_t nc = len * 2 + 16;
            int32_t *nb = realloc(imgbuf, (size_t)nc * sizeof(int32_t));
            if (!nb) { PyErr_NoMemory(); goto done; }
            imgbuf = nb;
            imgcap = nc;
        }
        for (k = 0; k < len; k++) {     /* the generators moving a point of the set */
            int32_t x = st.data[st.off[i] + k];
            PyObject *key = label_obj(x), *w;
            Py_ssize_t app;
            if (key == NULL)
                goto done;
            w = PyDict_GetItemWithError(who, key);
            if (w == NULL) {
                if (PyErr_Occurred())
                    goto done;
                continue;
            }
            if (!PyAnySet_CheckExact(w))
                goto use_python;
            app = set_ints(w, &idsbuf, &ids_cap, nids, &idobj, &nomem);
            if (app < 0) {
                if (nomem) { PyErr_NoMemory(); goto done; }
                goto use_python;
            }
            nids += app;
        }
        /* distinct ids, ascending (sorted through keys (id, index)) */
        if (nids > keycap) {
            Py_ssize_t nc = nids * 2 + 16;
            uint64_t *nk = realloc(idkeys, (size_t)nc * sizeof(uint64_t));
            uint64_t *nt;
            if (!nk) { PyErr_NoMemory(); goto done; }
            idkeys = nk;
            nt = realloc(idkeytmp, (size_t)nc * sizeof(uint64_t));
            if (!nt) { PyErr_NoMemory(); goto done; }
            idkeytmp = nt;
            keycap = nc;
        }
        if (nids > uobjcap) {
            Py_ssize_t nc = nids * 2 + 16;
            PyObject **no = realloc(uobj, (size_t)nc * sizeof(PyObject *));
            if (!no) { PyErr_NoMemory(); goto done; }
            uobj = no;
            uobjcap = nc;
        }
        for (k = 0; k < nids; k++)
            idkeys[k] = ((uint64_t)(uint32_t)idsbuf[k] << 32) | (uint64_t)k;
        sort_u64(idkeys, idkeytmp, nids);
        q = 0;
        for (k = 0; k < nids; k++) {
            int32_t id = (int32_t)(idkeys[k] >> 32);
            if (q == 0 || idsbuf[q - 1] != id) {
                /* (idsbuf[q - 1] was already overwritten by the ids kept so far) */
                uobj[q] = idobj[(Py_ssize_t)(idkeys[k] & 0xffffffffULL)];
                idsbuf[q++] = id;
            }
        }
        nids = q;
        for (k = 0; k < nids; k++) {
            PyObject *g = PyDict_GetItemWithError(gens, uobj[k]);
            Py_ssize_t idx;
            int isnew;
            int32_t ii;
            if (g == NULL) {
                if (PyErr_Occurred())
                    goto done;
                goto use_python;
            }
            if (!PyDict_CheckExact(g))
                goto use_python;
            for (q = 0; q < len; q++) {
                int32_t x = st.data[st.off[i] + q];
                PyObject *key = label_obj(x), *val;
                Py_ssize_t y;
                if (key == NULL)
                    goto done;
                val = PyDict_GetItemWithError(g, key);
                if (val == NULL) {
                    if (PyErr_Occurred())
                        goto done;
                    y = x;
                } else if (!read_small(val, &y) || y < 0) {
                    goto use_python;
                }
                imgbuf[q] = (int32_t)y;
            }
            sort_i32(imgbuf, len, &sortscratch, &sortcap);
            if (sortcap < 0) { PyErr_NoMemory(); goto done; }
            for (q = 0; q < len; q++)
                if (imgbuf[q] > maxlab)
                    maxlab = imgbuf[q];
            if (kind == 1 && (len != 2 || imgbuf[0] >= imgbuf[1]))
                goto use_python;
            idx = store_find(&st, imgbuf, len, &isnew);
            if (idx < 0) { PyErr_NoMemory(); goto done; }
            ii = (int32_t)idx;
            if (trip_n + 3 > trip_cap) {
                Py_ssize_t nc = trip_cap ? trip_cap * 2 : 256;
                int32_t *nt = realloc(trip, (size_t)nc * sizeof(int32_t));
                if (!nt) { PyErr_NoMemory(); goto done; }
                trip = nt;
                trip_cap = nc;
            }
            trip[trip_n++] = idsbuf[k];
            trip[trip_n++] = (int32_t)i;
            trip[trip_n++] = ii;
        }
    }
    if (ints_ensure(maxlab + 1) < 0)
        goto done;
    /* sort positions */
    order = malloc((size_t)(st.size ? st.size : 1) * sizeof(int32_t));
    rank_ = malloc((size_t)(st.size ? st.size : 1) * sizeof(int32_t));
    itmp = malloc((size_t)(st.size ? st.size : 1) * sizeof(int32_t));
    if (!order || !rank_ || !itmp) {
        PyErr_NoMemory();
        goto done;
    }
    for (i = 0; i < st.size; i++)
        order[i] = (int32_t)i;
    sort_sets(order, itmp, st.size, &st);
    for (i = 0; i < st.size; i++)
        rank_[order[i]] = (int32_t)i;
    if (ints_ensure(st.size) < 0)
        goto done;
    pos = PyList_New(st.size);
    table = PyDict_New();
    if (!pos || !table)
        goto done;
    for (i = 0; i < st.size; i++) {
        int32_t o = order[i];
        PyObject *obj;
        if (o < ns) {
            obj = seedobj[o];
            Py_INCREF(obj);
        } else {
            Py_ssize_t len = st.off[o + 1] - st.off[o], k;
            PyObject *t = PyTuple_New(len);
            if (!t)
                goto done;
            for (k = 0; k < len; k++) {
                Py_ssize_t v = st.data[st.off[o] + k];
                PyObject *ob;
                if (v < ints_cap) {
                    ob = int_ref(v);
                } else {
                    ob = PyLong_FromSsize_t(v);
                    if (!ob) { Py_DECREF(t); goto done; }
                }
                PyTuple_SET_ITEM(t, k, ob);
            }
            if (kind == 0) {
                obj = PyFrozenSet_New(t);
                Py_DECREF(t);
                if (!obj)
                    goto done;
            } else {
                obj = t;
            }
        }
        PyList_SET_ITEM(pos, i, obj);
    }
    for (i = 0; i < trip_n; i += 3) {
        Py_ssize_t id = trip[i];
        int32_t a = trip[i + 1], b = trip[i + 2];
        PyObject *idval, *mv;
        if (id < ints_cap) {
            idval = int_ref(id);
        } else {
            idval = PyLong_FromSsize_t(id);
            if (!idval)
                goto done;
        }
        mv = PyDict_GetItemWithError(table, idval);
        if (mv == NULL) {
            if (PyErr_Occurred()) {
                Py_DECREF(idval);
                goto done;
            }
            mv = PyDict_New();
            if (!mv || PyDict_SetItem(table, idval, mv) < 0) {
                Py_XDECREF(mv);
                Py_DECREF(idval);
                goto done;
            }
            Py_DECREF(mv);              /* (table holds it) */
        }
        Py_DECREF(idval);
        if (a != b) {
            PyObject *ka = int_ref(rank_[a]), *vb = int_ref(rank_[b]);
            int r = PyDict_SetItem(mv, ka, vb);
            Py_DECREF(ka);
            Py_DECREF(vb);
            if (r < 0)
                goto done;
        }
    }
    res = PyTuple_Pack(2, pos, table);
    goto done;
use_python:
    res = Py_None;
    Py_INCREF(res);
done:
    if (st_ok)
        store_free(&st);
    free(seedobj); free(imgbuf); free(idsbuf); free(idobj); free(order); free(rank_); free(itmp);
    free(trip); free(sortscratch); free(idkeys); free(idkeytmp); free(uobj);
    Py_XDECREF(pos);
    Py_XDECREF(table);
    return res;
}
/* ===== end of w23-speed2 block (3) ===== */

#define FAST(name) {#name, (PyCFunction)(void (*)(void))ck_##name, METH_FASTCALL, NULL}
static PyMethodDef methods[] = {
    FAST(set_fallbacks), FAST(mul), FAST(inv), FAST(act), FAST(maps), FAST(orbits),
    FAST(sift), FAST(sifts_to_id), FAST(make_fast_plan), FAST(wl2_single), FAST(wl2_check),
    /* w23-speed2 */
    FAST(wl_refine), FAST(class_plan), FAST(balls_new), FAST(balls_step),
    FAST(orbit_table), FAST(orbit_absorb),
    FAST(closure_dense),
    FAST(closure_sparse),
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
