#!/usr/bin/env python3
"""Drive headless Firefox over Marionette and take screenshots of video/index.html.
    shoot.py shots_dir "T1,T2,..."  [--w 1280 --h 860 --theme dark]
Each T is a time in seconds, or "chapterid" or "chapterid+offset". Prints page errors and state."""
import argparse, base64, json, os, socket, subprocess, sys, tempfile, time

class MN:
    def __init__(self, sock):
        self.s = sock; self.buf = b''; self.id = 0
    def recv(self):
        while True:
            if b':' in self.buf:
                head, rest = self.buf.split(b':', 1)
                n = int(head)
                if len(rest) >= n:
                    self.buf = rest[n:]
                    return json.loads(rest[:n].decode())
            d = self.s.recv(65536)
            if not d:
                raise IOError('connection closed')
            self.buf += d
    def send(self, name, params=None):
        self.id += 1
        msg = json.dumps([0, self.id, name, params or {}])
        data = f"{len(msg.encode())}:{msg}".encode()
        self.s.sendall(data)
        while True:
            r = self.recv()
            if isinstance(r, list) and r[0] == 1 and r[1] == self.id:
                if r[2]:
                    raise RuntimeError(str(r[2])[:500])
                return r[3]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('dir'); ap.add_argument('times')
    ap.add_argument('--w', type=int, default=1280); ap.add_argument('--h', type=int, default=860)
    ap.add_argument('--theme', default='dark'); ap.add_argument('--rm', default=None)
    ap.add_argument('--port', type=int, default=2829)
    ap.add_argument('--extra', default='')
    ap.add_argument('--profile', default=None)
    a = ap.parse_args()
    os.makedirs(a.dir, exist_ok=True)
    prof = a.profile or tempfile.mkdtemp(prefix='ffprof', dir=os.environ.get('FFTMP', '/tmp'))
    with open(os.path.join(prof, 'user.js'), 'w') as f:
        f.write(f'user_pref("marionette.port", {a.port});\nuser_pref("browser.shell.checkDefaultBrowser", false);\nuser_pref("datareporting.policy.dataSubmissionEnabled", false);\nuser_pref("browser.startup.homepage_override.mstone","ignore");\nuser_pref("toolkit.telemetry.reportingpolicy.firstRun", false);\n')
    env = dict(os.environ, MOZ_HEADLESS='1', MOZ_HEADLESS_WIDTH=str(a.w), MOZ_HEADLESS_HEIGHT=str(a.h))
    proc = subprocess.Popen(['/run/current-system/sw/bin/firefox', '--marionette', '--headless', '--no-remote', '--profile', prof], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=env)
    try:
        sock = None
        for i in range(120):
            try:
                sock = socket.create_connection(('127.0.0.1', a.port), timeout=3); break
            except OSError:
                time.sleep(0.5)
        if sock is None:
            print('could not connect to marionette'); return 1
        sock.settimeout(60)
        mn = MN(sock)
        hello = mn.recv()
        mn.send('WebDriver:NewSession', {'capabilities': {'alwaysMatch': {'acceptInsecureCerts': True}}})
        try: mn.send('WebDriver:SetWindowRect', {'x': 0, 'y': 0, 'width': a.w, 'height': a.h})
        except Exception as e: print('resize warn', e)
        index = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'index.html')
        url = 'file://' + index + '?shot=1&theme=' + a.theme + (('&rm=' + a.rm) if a.rm else '') + (('&' + a.extra) if a.extra else '')
        mn.send('WebDriver:Navigate', {'url': url})
        for i in range(60):
            v = mn.send('WebDriver:ExecuteScript', {'script': 'return window.V && window.V.ready === true', 'sandbox': None})
            if v.get('value') is True: break
            time.sleep(0.5)
        state = mn.send('WebDriver:ExecuteScript', {'script': 'return JSON.stringify(window.__state())', 'sandbox': None})['value']
        st = json.loads(state)
        print('duration', round(st['T'], 1), 'chapters', len(st['chapters']), 'scenes', st['scenes'])
        chmap = {c[0]: c for c in st['chapters']}
        times = []
        for tok in a.times.split(','):
            tok = tok.strip()
            if not tok: continue
            try:
                times.append((tok.replace('.', '_').replace('+', '_p'), float(tok)))
            except ValueError:
                cid, _, off = tok.partition('+')
                base = chmap[cid][1]
                offs = float(off) if off else 0.01
                times.append((f'{cid}_p{off or "0"}'.replace('.', '_'), base + offs))
        for name, t in times:
            mn.send('WebDriver:ExecuteScript', {'script': f'window.__seek({t});', 'sandbox': None})
            time.sleep(0.25)
            shot = mn.send('WebDriver:TakeScreenshot', {'full': False, 'hash': False})
            data = shot['value'] if isinstance(shot, dict) else shot
            with open(os.path.join(a.dir, name + '.png'), 'wb') as f:
                f.write(base64.b64decode(data))
        errs = mn.send('WebDriver:ExecuteScript', {'script': 'return JSON.stringify(window.__errors||[])', 'sandbox': None})['value']
        print('errors:', errs)
        mn.send('WebDriver:DeleteSession', {})
    finally:
        proc.terminate()
        try: proc.wait(5)
        except Exception: proc.kill()
    return 0

if __name__ == '__main__':
    sys.exit(main())
