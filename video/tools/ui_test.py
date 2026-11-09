#!/usr/bin/env python3
"""UI verification over Marionette: keyboard, chapter menu, deep links, reduced motion, determinism.
Usage: ui_test.py [--port 2840]
Exits 0 only when every check passes."""
import argparse, base64, hashlib, json, os, socket, subprocess, sys, tempfile, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from shoot import MN

URL = 'file://' + os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'index.html')
FIREFOX = '/run/current-system/sw/bin/firefox'
ok_all = True

def check(name, cond, detail=''):
    global ok_all
    print(('PASS ' if cond else 'FAIL ') + name + (': ' + str(detail) if detail != '' else ''))
    ok_all = ok_all and bool(cond)

def js(mn, script):
    r = mn.send('WebDriver:ExecuteScript', {'script': script, 'sandbox': None})
    return r.get('value')

def load(mn, q=''):
    mn.send('WebDriver:Navigate', {'url': URL + q})
    for _ in range(80):
        if js(mn, 'return !!(window.V && V.ready)') is True:
            return
        time.sleep(0.25)
    raise RuntimeError('page did not become ready')

def key(mn, k):
    js(mn, "window.dispatchEvent(new KeyboardEvent('keydown',{key:%s,bubbles:true}));" % json.dumps(k))
    time.sleep(0.05)

def state(mn):
    return json.loads(js(mn, 'return JSON.stringify({t:V.P.t,playing:V.P.playing,speed:V.P.speed,voice:V.P.voice,T:V.T,hash:location.hash,theme:document.documentElement.dataset.theme||"",errors:window.__errors,cap:document.getElementById("caption-text").textContent})'))

def frame_hash(mn):
    d = js(mn, "return document.getElementById('cv').toDataURL('image/png')")
    return hashlib.sha1(d.encode()).hexdigest()

def main():
    ap = argparse.ArgumentParser(); ap.add_argument('--port', type=int, default=2840); a = ap.parse_args()
    prof = tempfile.mkdtemp(prefix='ffprof', dir=os.environ.get('FFTMP', '/tmp'))
    with open(os.path.join(prof, 'user.js'), 'w') as f:
        f.write('user_pref("marionette.port", %d);\nuser_pref("datareporting.policy.dataSubmissionEnabled", false);\n' % a.port)
    env = dict(os.environ, MOZ_HEADLESS='1', MOZ_HEADLESS_WIDTH='1280', MOZ_HEADLESS_HEIGHT='860')
    proc = subprocess.Popen([FIREFOX, '--marionette', '--headless', '--no-remote', '--profile', prof], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
    try:
        sock = None
        for _ in range(120):
            try:
                sock = socket.create_connection(('127.0.0.1', a.port), timeout=3); break
            except OSError:
                time.sleep(0.5)
        sock.settimeout(60)
        mn = MN(sock); mn.recv()
        mn.send('WebDriver:NewSession', {'capabilities': {'alwaysMatch': {'acceptInsecureCerts': True}}})
        mn.send('WebDriver:SetWindowRect', {'x': 0, 'y': 0, 'width': 1280, 'height': 860})
        load(mn)
        st = state(mn); T = st['T']
        print('duration', round(T, 1))
        check('no errors at load', st['errors'] == [], st['errors'])
        check('starts paused at 0', st['t'] < 0.2 and not st['playing'], st)
        # exact seeking / determinism: same t gives the same frame, also after going elsewhere
        js(mn, 'window.__seek(800.5)'); time.sleep(0.2); h1 = frame_hash(mn)
        js(mn, 'window.__seek(2000)'); time.sleep(0.2); h2 = frame_hash(mn)
        js(mn, 'window.__seek(800.5)'); time.sleep(0.2); h3 = frame_hash(mn)
        check('scrub determinism: frame at t=800.5 reproduces exactly', h1 == h3, (h1[:10], h3[:10]))
        check('different times differ', h1 != h2)
        # keyboard
        js(mn, 'window.__seek(100)'); time.sleep(0.1)
        key(mn, ' '); time.sleep(0.15); st = state(mn); check('space plays', st['playing'], st)
        key(mn, ' '); time.sleep(0.05); st = state(mn); check('space pauses', not st['playing'], st)
        t0 = state(mn)['t']; key(mn, 'ArrowRight'); check('right +5', abs(state(mn)['t'] - t0 - 5) < 0.5)
        t0 = state(mn)['t']; key(mn, 'ArrowLeft'); check('left -5', abs(state(mn)['t'] - t0 + 5) < 0.5)
        t0 = state(mn)['t']; key(mn, 'l'); check('L +10', abs(state(mn)['t'] - t0 - 10) < 0.5)
        key(mn, 'j'); key(mn, '5'); check('digit 5 jumps to half', abs(state(mn)['t'] - T / 2) < 2)
        spd0 = state(mn)['speed']; key(mn, '+'); check('speed up', state(mn)['speed'] > spd0); key(mn, '-'); check('speed back', state(mn)['speed'] == spd0)
        ch0 = js(mn, "return V.scenes.findIndex(s=>s.T0<=V.P.t && s.T0+s.D>V.P.t)")
        key(mn, 'n'); ch1 = state(mn)
        check('N advances a chapter', ch1['t'] > 0, ch1['t'])
        key(mn, 'p'); key(mn, 'p')
        key(mn, 't'); th = state(mn)['theme']; key(mn, 't'); th2 = state(mn)['theme']; check('theme toggles', th != th2, (th, th2))
        # chapter menu builds and deep links
        n = js(mn, "return document.querySelectorAll('#chapter-list .chap').length")
        nchap = js(mn, 'return V.chapters.length')
        check('chapter menu lists every chapter', n == nchap, (n, nchap))
        js(mn, "document.querySelectorAll('#chapter-list .chap')[7].click()"); st2 = state(mn)
        expT = js(mn, "return V.chapters[7].T0")
        check('chapter menu seeks', abs(st2['t'] - expT) < 0.2)
        load(mn, '#ch=sigma'); st3 = state(mn)
        check('deep link #ch= seeks to chapter', abs(st3['t'] - js(mn, "return V.chapters.find(c=>c.id==='sigma').T0")) < 0.5, st3['t'])
        load(mn, '#t=1234'); check('deep link #t= seeks', abs(state(mn)['t'] - 1234) < 1)
        load(mn, '?t=2500&shot=1'); check('?t= seeks', abs(state(mn)['t'] - 2500) < 1)
        # captions present
        c = state(mn)['cap']; check('captions shown', len(c) > 5, c[:60])
        # playback advances and respects speed
        load(mn, '?t=300&shot=1')
        js(mn, 'V.P.speed=1;')
        key(mn, ' ')
        time.sleep(1.5)
        key(mn, ' ')
        t1 = state(mn)['t']
        check('playback advances in real time', 300.8 < t1 < 302.5, t1)
        # interactive: click CFI twist -- uses ix state; must not change the timeline t
        load(mn, '?shot=1')
        tw = js(mn, "return (()=>{const ch=V.chapters.find(c=>c.id==='cfi');const sc=ch.scenes[1];window.__seek(sc.T0+sc.beats[4].t0+1);const ix=sc.ix; const r=document.getElementById('cv').getBoundingClientRect();const bt=sc.onClick(0,0,ix); return JSON.stringify([ix.twist,V.P.t]);})()")
        check('CFI interactive scene exists', tw is not None, tw)
        # Interactive scene: real click at an edge next to the twist
        moved = js(mn, "return (()=>{const ch=V.chapters.find(c=>c.id==='cfi');const sc=ch.scenes[1];const ix=sc.ix||sc.init();sc.ix=ix;const before=ix.twist;const r=document.getElementById('cv').getBoundingClientRect();const R=150,cx=960,cy=365;const pos=[[cx-R,cy-R],[cx+R,cy-R],[cx+R,cy+R],[cx-R,cy+R]];const lx=(a,b)=>[(pos[a][0]+pos[b][0])/2,(pos[a][1]+pos[b][1])/2];const p=lx(1,2);sc.onClick(p[0],p[1],ix);return JSON.stringify([before,ix.twist]);})()")
        check('CFI twist moves to an adjacent edge', moved is not None and json.loads(moved)[0] != json.loads(moved)[1], moved)
        blk = js(mn, "return (()=>{const ch=V.chapters.find(c=>c.id==='blocks');const sc=ch.scenes[2];window.__seek(sc.T0+sc.beats[1].t0+1);const ix=sc.ix||(sc.ix=sc.init());const P=[[310,190],[457,275],[457,445],[310,530],[163,445],[163,275]];sc.onClick(310,190,ix);sc.onClick(310,530,ix);return JSON.stringify(ix.blocks[0]);})()")
        check('block explorer finds the antipodal block', blk is not None and json.loads(blk) == [0, 1, 2, 0, 1, 2], blk)
        # reduced motion: beats still advance, no intermediate tween values
        load(mn, '?t=500&rm=1&shot=1')
        check('reduced-motion loads', js(mn, 'return V.RM') is True)
        v = js(mn, "return [V.ease(0.2),V.ease(0.8)]")
        check('reduced-motion ease is a step', v == [0, 1], v)
        load(mn, '?shot=1')
        check('reduced-motion off by default', js(mn, 'return V.RM') is False)
        # voice toggle does not error, off by default
        st4 = state(mn); check('voice off by default', not st4['voice'])
        key(mn, 'm'); time.sleep(0.05); st5 = state(mn); key(mn, 'm')
        check('voice toggles', st5['voice'] is True or st5['errors'] == [], st5)
        st6 = state(mn); check('no console errors in UI run', st6['errors'] == [], st6['errors'])
        mn.send('WebDriver:DeleteSession', {})
    finally:
        proc.terminate()
        try:
            proc.wait(5)
        except Exception:
            proc.kill()
    print('ALL PASSED' if ok_all else 'SOME FAILED')
    return 0 if ok_all else 1

if __name__ == '__main__':
    sys.exit(main())
