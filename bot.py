"""Survival-first mech bot: hide in low-exposure cover inside the next zone, fight only when needed."""
import math, random, sys, time
import mechfight as mf
from geo import Map, AStar

TAU = 2 * math.pi
UPG_ORDER = ['armor', 'plating', 'nanites', 'laser_damage', 'laser_charge', 'gun_rate', 'gun_damage',
             'sensors', 'servos', 'lightning_efficiency', 'lightning_range', 'mortar_reload', 'capacitor',
             'reactor', 'jets', 'gyros', 'gun_mag', 'gun_velocity', 'lightning_chain', 'mortar_splash',
             'mortar_velocity', 'laser_pierce']
WPREF = {'laser': 3, 'lightning': 2, 'mortar': 1, 'gun': 0}


def angdiff(a, b):
    d = (a - b) % TAU
    return d - TAU if d > math.pi else d


def log(*a):
    print(*a, file=sys.stderr)


class Bot:
    name = "hide-and-seek"

    def __init__(self, hello):
        self.cfg = hello['config']
        self.id = hello['slot']
        random.seed(hello.get('seed', 0))
        self.m = Map()
        self.enemies = {}        # id -> dict(pos, vel, t, hp, max_hp, weapons, aim, charging, cubes)
        self.npcs = {}
        self.attackers = {}      # id -> (t, bearing, amount)
        self.sounds = []         # (t, kind, bearing, dist)
        self.dmg_log = []        # (t, amount)
        self.last_dmg_t = -99
        self.last_hit_t = -99
        self.hide = None         # (x, y)
        self.hide_cell = None
        self.hide_t = -99
        self.hide_key = None
        self.goal = None         # (x, y) current nav goal
        self.goal_cell = None
        self.planner = None
        self.path = None
        self.path_i = 0
        self.plan_goal = None
        self.bad_cells = set()
        self.pos_hist = []
        self.stuck_until = -1
        self.stuck_dir = 1
        self.jink_t = 0
        self.jink_s = 1
        self.scan_dirs = None
        self.scan_for = None
        self.cover = None
        self.cover_t = -99
        self.prev_hp = None
        self.failed_take = {}
        self.npc_home = {}
        self.t = 0
        self.mode = 'start'

    # ------------------------------------------------------------------ utils
    def my_center(self, me):
        p = me['pos']; return (p[0], p[1], p[2] + me['stats'].get('height', 9) * 0.5)

    def zone_at(self, z, t):
        if t <= z['shrink_start']:
            return z['center'], z['radius']
        if t >= z['shrink_end']:
            return z['next_center'], z['next_radius']
        f = (t - z['shrink_start']) / max(1e-6, z['shrink_end'] - z['shrink_start'])
        c = [z['center'][0] + (z['next_center'][0] - z['center'][0]) * f,
             z['center'][1] + (z['next_center'][1] - z['center'][1]) * f]
        return c, z['radius'] + (z['next_radius'] - z['radius']) * f

    def in_circle(self, p, c, r, margin=0.0):
        return (p[0] - c[0]) ** 2 + (p[1] - c[1]) ** 2 <= max(0.0, r - margin) ** 2

    # ------------------------------------------------------------------ memory
    def update_memory(self, obs):
        t = obs['t']; me = obs['self']
        for a in obs['mechs']:
            d = dict(pos=a['pos'], vel=a['vel'], t=t, hp=a.get('hp', 1400), max_hp=a.get('max_hp', 1400),
                     weapons=a.get('weapons', []), aim=a['aim'], charging=a.get('charging', False),
                     cubes=a.get('cubes', 0), id=a['id'], kind=a['kind'])
            if a['kind'] == 'mech':
                self.enemies[a['id']] = d
            else:
                self.npcs[a['id']] = d
                if a['id'] not in self.npc_home:
                    self.npc_home[a['id']] = (a['pos'][0], a['pos'][1])
        for k in [k for k, v in self.enemies.items() if t - v['t'] > 20]:
            del self.enemies[k]
        for k in [k for k, v in self.npcs.items() if t - v['t'] > 20]:
            del self.npcs[k]
        for e in obs['events']:
            ty = e['type']
            if ty == 'damaged':
                if e.get('by') is not None:
                    self.attackers[e['by']] = (t, e.get('bearing'), e.get('amount', 0))
                    self.last_dmg_t = t
                self.dmg_log.append((t, e.get('amount', 0), e.get('by')))
            elif ty == 'hit':
                self.last_hit_t = t
            elif ty == 'take_failed':
                self.failed_take[e['id']] = t
            elif ty == 'kill':
                self.enemies.pop(e.get('target'), None)
        self.dmg_log = [d for d in self.dmg_log if t - d[0] < 6]
        for s in obs['sounds']:
            self.sounds.append((t - s.get('age', 0), s['kind'], s['bearing'], s['dist']))
        self.sounds = [s for s in self.sounds if t - s[0] < 6]
        for k in [k for k, v in self.attackers.items() if t - v[0] > 15]:
            del self.attackers[k]

    def dps_in(self, t, window=3.0, mechs_only=True):
        s = sum(a for (tt, a, by) in self.dmg_log if t - tt < window and (by is not None) and (not mechs_only or by < 100))
        return s / window

    # ------------------------------------------------------------------ offers / loot
    def choose_offer(self, offer):
        ids = [c['id'] for c in offer['choices']]
        for u in UPG_ORDER:
            if u in ids:
                return ids.index(u)
        return 0

    def want_pickup(self, me, kind):
        ws = me['weapons']
        kinds = [w['kind'] for w in ws if w]
        if kind in kinds or kind == 'gun':
            return None
        if ws[1] is None:
            return {}
        if ws[0] is None:
            return {}
        # both full: swap slot holding the least preferred non-gun weapon if this is better
        cand = [(WPREF[w['kind']], i) for i, w in enumerate(ws) if w and w['kind'] != 'gun']
        if not cand:
            return None
        v, i = min(cand)
        if WPREF[kind] > v:
            w = ws[i]
            if w['kind'] == 'laser' and w.get('charge', 0) > 0:
                return None
            return {'drop': i}
        return None

    # ------------------------------------------------------------------ hide spot
    def pick_hide(self, obs, me):
        m = self.m; z = obs['zone']; t = obs['t']
        nc, nr = z['next_center'], z['next_radius']
        cc, cr = self.zone_at(z, t)
        px, py = me['pos'][0], me['pos'][1]
        margin = max(6.0, min(35.0, 0.22 * nr))
        if nr < 4:
            return (nc[0], nc[1])
        avoid = []
        for d in obs.get('drops', []):
            avoid.append((d['pos'][0], d['pos'][1], 70.0, 60.0))
        for e in self.enemies.values():
            if t - e['t'] < 30:
                avoid.append((e['pos'][0], e['pos'][1], 70.0, 40.0))
        for k, (hx, hy) in self.npc_home.items():
            if k in self.npcs:
                avoid.append((hx, hy, 70.0, 35.0))
        best = None; bs = 1e18; n = 0
        r2 = max(0.0, nr - margin) ** 2
        cr2 = max(0.0, cr - margin * 0.5) ** 2
        for (e, c) in m.cells_sorted:
            if c in self.bad_cells:
                continue
            x, y = m.cell_xy(c)
            if (x - nc[0]) ** 2 + (y - nc[1]) ** 2 > r2:
                continue
            if (x - cc[0]) ** 2 + (y - cc[1]) ** 2 > cr2:
                continue
            d = math.hypot(x - px, y - py)
            s = e * 0.6 + d * 0.12
            for (ax, ay, ar, ap) in avoid:
                dd = (x - ax) ** 2 + (y - ay) ** 2
                if dd < ar * ar:
                    s += ap * (1 - math.sqrt(dd) / ar)
            if s < bs:
                bs = s; best = c
            n += 1
            if n > 6000 and best is not None:
                break
        if best is None:
            c = m.nearest_walk(nc[0], nc[1], 30)
            if c is None:
                return (nc[0], nc[1])
            best = c
        self.hide_cell = best
        return m.cell_xy(best)

    # ------------------------------------------------------------------ navigation
    def set_goal(self, gx, gy, me, expw=1.5):
        m = self.m
        if self.goal and math.hypot(self.goal[0] - gx, self.goal[1] - gy) < 3 and (self.planner or self.path):
            return
        self.goal = (gx, gy)
        s = m.nearest_walk(me['pos'][0], me['pos'][1], 6)
        g = m.nearest_walk(gx, gy, 10)
        self.path = None; self.path_i = 0
        if s is None or g is None:
            self.planner = None
            return
        avoid = []
        for e in self.enemies.values():
            if self.t - e['t'] < 10:
                avoid.append((e['pos'][0], e['pos'][1], 50.0, 30.0))
        self.planner = AStar(m, s, g, expw=expw, avoid=avoid)

    def nav_dir(self, me, budget):
        """Returns unit move vector toward goal (or None if arrived)."""
        m = self.m
        px, py = me['pos'][0], me['pos'][1]
        if self.goal is None:
            return None
        gx, gy = self.goal
        dist = math.hypot(gx - px, gy - py)
        if dist < 2.0:
            return None
        if self.planner is not None and not self.planner.done:
            self.planner.step(budget)
            if self.planner.done:
                if self.planner.path:
                    self.path = [m.cell_xy(c) for c in self.planner.path] + [self.goal]
                    self.path_i = 0
                else:
                    self.bad_cells.add(self.planner.goal)
                    self.path = None
                self.planner = None
        if self.path:
            # advance along path; pick furthest directly walkable waypoint (lookahead 8)
            while self.path_i < len(self.path) - 1 and math.hypot(self.path[self.path_i][0] - px, self.path[self.path_i][1] - py) < 3.0:
                self.path_i += 1
            best = self.path_i
            for k in range(min(len(self.path) - 1, self.path_i + 8), self.path_i, -1):
                if m.walk_line((px, py), self.path[k]):
                    best = k; break
            # if we drifted far from path, replan
            wx, wy = self.path[best]
            if math.hypot(wx - px, wy - py) > 30:
                g = self.goal; self.goal = None; self.set_goal(g[0], g[1], me)
            self.path_i = best
            d = math.hypot(wx - px, wy - py)
            if d < 1e-3:
                return None
            return ((wx - px) / d, (wy - py) / d)
        # no path yet: head straight
        return ((gx - px) / dist, (gy - py) / dist)

    def path_remaining(self, me):
        if not self.path:
            if self.goal:
                return math.hypot(self.goal[0] - me['pos'][0], self.goal[1] - me['pos'][1]) * 1.3
            return 0
        px, py = me['pos'][0], me['pos'][1]
        L = 0; prev = (px, py)
        for p in self.path[self.path_i:]:
            L += math.hypot(p[0] - prev[0], p[1] - prev[1]); prev = p
        return L

    # ------------------------------------------------------------------ cover
    def find_cover(self, me, threats, t):
        m = self.m; px, py = me['pos'][0], me['pos'][1]
        eyes = [(e['pos'][0], e['pos'][1], e['pos'][2] + 8) for e in threats]
        z = self.cur_zone
        best = None; bs = 1e9
        for r in (8, 14, 22, 32, 44):
            for k in range(16):
                a = k * TAU / 16 + (r * 0.1)
                x = px + math.cos(a) * r; y = py + math.sin(a) * r
                c = m.nearest_walk(x, y, 1)
                if c is None:
                    continue
                cx, cy = m.cell_xy(c)
                if z and not self.in_circle((cx, cy), z[0], z[1], 4):
                    continue
                gz = m.ground(cx, cy)
                hidden = True
                for ey in eyes:
                    if m.los(ey, (cx, cy, gz + 5.0)) or m.los(ey, (cx, cy, gz + 8.5)):
                        hidden = False; break
                if not hidden:
                    continue
                s = r + m.E[c] / 254.0 * 30
                # prefer moving away from threats
                for e in threats:
                    de = math.hypot(cx - e['pos'][0], cy - e['pos'][1])
                    if de < 30:
                        s += (30 - de) * 2
                if s < bs:
                    bs = s; best = (cx, cy)
            if best is not None and r >= 14:
                break
        return best

    # ------------------------------------------------------------------ aiming
    def solve_lead(self, src, tgt_pos, tgt_vel, speed, extra=0.075):
        p = list(tgt_pos)
        t = 0
        for _ in range(3):
            d = math.dist(src, p)
            t = d / speed + extra
            p = [tgt_pos[0] + tgt_vel[0] * t, tgt_pos[1] + tgt_vel[1] * t, tgt_pos[2] + max(-10, min(10, tgt_vel[2])) * t * 0.5]
        return p, t

    def aim_to(self, src, p):
        dx = p[0] - src[0]; dy = p[1] - src[1]; dz = p[2] - src[2]
        return [math.atan2(dy, dx), math.atan2(dz, math.hypot(dx, dy))]

    def ballistic(self, src, p, v, g, high=False):
        dx = p[0] - src[0]; dy = p[1] - src[1]; dz = p[2] - src[2]
        d = math.hypot(dx, dy)
        v2 = v * v; disc = v2 * v2 - g * (g * d * d + 2 * dz * v2)
        if disc < 0 or d < 1:
            return None
        r = math.sqrt(disc)
        th = math.atan2(v2 + r if high else v2 - r, g * d)
        tof = d / max(1e-3, v * math.cos(th))
        return [math.atan2(dy, dx), th], tof

    # ------------------------------------------------------------------ main
    def act(self, obs):
        t0 = time.perf_counter()
        t = obs['t']; self.t = t
        me = obs['self']; st = me['stats']
        pos = me['pos']; px, py, pz = pos
        self.update_memory(obs)
        z = obs['zone']
        self.cur_zone = self.zone_at(z, t)
        act = {}
        if obs.get('offer'):
            act['pick'] = self.choose_offer(obs['offer'])

        hpf = me['hp'] / max(1, me['max_hp'])
        h_me = st.get('height', 9)
        center = (px, py, pz + h_me * 0.5)
        eye = (px, py, pz + st.get('eye_height', 8))
        muzzle = (px, py, pz + st.get('muzzle_height', 7))
        weapons = me['weapons']
        kinds = [w['kind'] if w else None for w in weapons]
        has = {k: i for i, k in enumerate(kinds) if k}

        # ---------- visible enemies & threats
        vis = []
        for a in obs['mechs']:
            if a['kind'] != 'mech':
                continue
            ap = a['pos']; d = math.dist(ap, pos)
            tc = (ap[0], ap[1], ap[2] + 9 * (1 + 0.05 * a.get('cubes', 0)) * 0.5)
            shoot_los = self.m.los(muzzle, tc)
            e_eye = (ap[0], ap[1], ap[2] + 8 * (1 + 0.05 * a.get('cubes', 0)))
            they_see = self.m.los(e_eye, center) or self.m.los(e_eye, (px, py, pz + h_me * 0.95))
            yaw_to_me = math.atan2(py - ap[1], px - ap[0])
            aimed = abs(angdiff(a['aim'][0], yaw_to_me)) < 0.35
            att = a['id'] in self.attackers and t - self.attackers[a['id']][0] < 4
            vis.append(dict(a=a, d=d, tc=tc, los=shoot_los, they_see=they_see, aimed=aimed, att=att))
        threats = [v for v in vis if (v['they_see'] and (v['aimed'] or v['d'] < 60)) or v['att']]
        dps_in = self.dps_in(t)
        under_fire = t - self.last_dmg_t < 2.0 and dps_in > 0

        # ---------- weapons readiness
        laser_i = has.get('laser'); gun_i = has.get('gun'); mort_i = has.get('mortar'); lig_i = has.get('lightning')
        my_dps = 0
        if gun_i is not None: my_dps += 90
        if laser_i is not None: my_dps += 110
        if lig_i is not None: my_dps += 120
        if mort_i is not None: my_dps += 60
        my_dps *= 1 + 0.04 * min(me['cubes'], 10)

        # ---------- target selection
        target = None; tscore = -1e9
        for v in vis:
            a = v['a']
            if not v['los'] or v['d'] > 230:
                continue
            ehp = a.get('hp', 1400)
            s = -v['d'] * 0.5 - ehp * 0.05
            if v['att']: s += 80
            if v['aimed'] and v['they_see']: s += 40
            if ehp < 400: s += 50
            engage = v['att'] or (v['they_see'] and v['aimed']) or v['d'] < 70 or (ehp < 450 and v['d'] < 140) \
                or (hpf > 0.7 and v['d'] < 120 and len(vis) == 1)
            if not engage:
                continue
            if s > tscore:
                tscore = s; target = v
        # NPCs: shoot if they attack us or are close
        npc_t = None
        if target is None:
            for a in obs['mechs']:
                if a['kind'] != 'npc':
                    continue
                d = math.dist(a['pos'], pos)
                att = a['id'] in self.attackers and t - self.attackers[a['id']][0] < 5
                quiet = all(t - e['t'] > 8 for e in self.enemies.values())
                if att or d < 40 or (quiet and d < 70 and t < 330):
                    tc = (a['pos'][0], a['pos'][1], a['pos'][2] + 1.75)
                    if self.m.los(muzzle, tc) and (npc_t is None or d < npc_t['d']):
                        npc_t = dict(a=a, d=d, tc=tc, los=True, npc=True)
        crate_t = None
        if target is None and npc_t is None and t < 240:
            quiet = all(t - e['t'] > 8 for e in self.enemies.values())
            if quiet:
                for c in obs['crates']:
                    d = math.dist(c['pos'], pos)
                    if d < 55:
                        tc = (c['pos'][0], c['pos'][1], c['pos'][2] + 1.2)
                        if self.m.los(muzzle, tc) and (crate_t is None or d < crate_t['d']):
                            crate_t = dict(a=dict(pos=c['pos'], vel=[0, 0, 0], id=c['id']), d=d, tc=tc, los=True, crate=True)
        shoot = target or npc_t or crate_t

        # ---------- decide movement mode
        mode = 'hide'
        cur_c, cur_r = self.cur_zone
        out_now = not me['in_zone']
        move_goal = None
        want_still = False

        # fight-or-flight
        losing = False
        if threats:
            ehp = sum(v['a'].get('hp', 1400) for v in threats)
            edps = sum(80 + (110 if 'laser' in v['a'].get('weapons', []) else 0) + (100 if 'lightning' in v['a'].get('weapons', []) and v['d'] < 50 else 0) for v in threats)
            edps = max(edps, dps_in)
            my_time = me['hp'] / max(1, edps); their_time = ehp / max(1, my_dps)
            losing = my_time < their_time * 1.3 or hpf < 0.45 or len(threats) >= 2
        if threats and losing:
            if self.cover is None or t - self.cover_t > 1.0:
                self.cover = self.find_cover(me, [v['a'] for v in threats], t); self.cover_t = t
            if self.cover:
                mode = 'cover'; move_goal = self.cover
        elif not threats and under_fire:
            # hit by something unseen: move to new spot (reconsider hide)
            if t - self.hide_t > 4:
                self.hide = None
        if mode == 'hide' and threats and not losing:
            mode = 'fight'

        # loot / cubes when no threats
        take_id = None; take_drop = None
        for p in obs['pickups']:
            if self.failed_take.get(p['id'], -99) > t - 3:
                continue
            w = self.want_pickup(me, p['kind'])
            if w is None:
                continue
            d = math.hypot(p['pos'][0] - px, p['pos'][1] - py)
            if abs(p['pos'][2] - pz) > 3.5:
                continue
            if d < 3.8:
                take_id = p['id']; take_drop = w.get('drop')
            elif mode == 'hide' and not under_fire and d < 80 and self.in_circle(p['pos'], cur_c, cur_r, 10):
                if move_goal is None or d < math.hypot(move_goal[0] - px, move_goal[1] - py):
                    move_goal = (p['pos'][0], p['pos'][1]); mode = 'loot'
        if take_id is not None:
            act['take'] = take_id
            if take_drop is not None:
                act['drop'] = take_drop
        if mode == 'hide':
            for c in obs['cubes']:
                d = math.hypot(c['pos'][0] - px, c['pos'][1] - py)
                if d < 60 and abs(c['pos'][2] - pz) < 3.5 and self.in_circle(c['pos'], cur_c, cur_r, 8) and not under_fire:
                    if move_goal is None or d < math.hypot(move_goal[0] - px, move_goal[1] - py):
                        move_goal = (c['pos'][0], c['pos'][1]); mode = 'cube'
        # supply drop: go capture if near, quiet, and healthy-ish
        if mode == 'hide':
            for dr in obs.get('drops', []):
                d = math.hypot(dr['pos'][0] - px, dr['pos'][1] - py)
                quiet = all(t - e['t'] > 6 for e in self.enemies.values())
                if dr['lands_in'] <= 2 and d < 90 and quiet and (dr.get('holder') in (None, self.id)) and self.in_circle(dr['pos'], cur_c, cur_r, 5):
                    move_goal = (dr['pos'][0], dr['pos'][1]); mode = 'drop'

        # hide spot maintenance
        zkey = (round(z['next_center'][0]), round(z['next_center'][1]), round(z['next_radius']))
        if self.hide is None or self.hide_key != zkey or (under_fire and not threats and t - self.hide_t > 4) \
                or not self.in_circle(self.hide, cur_c, cur_r, 3):
            if time.perf_counter() - t0 < 0.015:
                self.hide = self.pick_hide(obs, me); self.hide_key = zkey; self.hide_t = t
                self.scan_dirs = None
        if mode in ('hide', 'fight') and self.hide:
            move_goal = self.hide

        # ---------- movement
        mv = (0.0, 0.0); boost = False; jump = False
        budget = max(0.002, 0.018 - (time.perf_counter() - t0))
        at_hide = False
        if move_goal is not None:
            if mode in ('loot', 'cube', 'drop') or mode == 'cover':
                if math.hypot(move_goal[0] - px, move_goal[1] - py) < 25 and self.m.walk_line((px, py), move_goal):
                    self.goal = move_goal; self.planner = None; self.path = [move_goal]; self.path_i = 0
                else:
                    self.set_goal(move_goal[0], move_goal[1], me)
            else:
                self.set_goal(move_goal[0], move_goal[1], me)
            dvec = self.nav_dir(me, budget)
            if dvec is None:
                at_hide = (mode == 'hide' or mode == 'fight')
                if mode == 'drop' or mode in ('loot', 'cube'):
                    dx = move_goal[0] - px; dy = move_goal[1] - py; dd = math.hypot(dx, dy)
                    if dd > 0.5:
                        mv = (dx / dd * 0.6, dy / dd * 0.6)
            else:
                mv = dvec
        # zone urgency
        rem = self.path_remaining(me) if move_goal is not None else 0
        speed = st.get('walk_speed', 11.7)
        if out_now:
            boost = me['energy'] > 10
            if move_goal is None or at_hide:
                dx = z['next_center'][0] - px; dy = z['next_center'][1] - py; dd = math.hypot(dx, dy) or 1
                mv = (dx / dd, dy / dd)
        else:
            # time until the zone edge reaches us
            tl = 1e9
            for dt in (5, 10, 15, 20, 30, 45):
                c2, r2 = self.zone_at(z, t + dt)
                if not self.in_circle(pos, c2, r2, 2):
                    tl = dt; break
            if rem / speed > tl - 3 and me['energy'] > 25:
                boost = True
        if mode == 'cover' and me['energy'] > 20:
            boost = True
        if mode in ('loot', 'cube') and threats == [] and me['energy'] > 60 and rem > 40:
            boost = True

        # jink when exposed
        exposed = [v for v in vis if v['they_see'] and v['d'] < 220]
        if exposed and mode != 'hide':
            if t > self.jink_t:
                self.jink_t = t + random.uniform(0.35, 0.9); self.jink_s = random.choice((-1, 1))
            v0 = min(exposed, key=lambda v: v['d'])
            by = math.atan2(v0['a']['pos'][1] - py, v0['a']['pos'][0] - px)
            perp = (math.cos(by + math.pi / 2) * self.jink_s, math.sin(by + math.pi / 2) * self.jink_s)
            if mv == (0.0, 0.0):
                mv = perp
            else:
                mv = (mv[0] * 0.8 + perp[0] * 0.6, mv[1] * 0.8 + perp[1] * 0.6)
        elif exposed and at_hide:
            # spotted at our hide spot: strafe a little around it
            if t > self.jink_t:
                self.jink_t = t + random.uniform(0.4, 0.9); self.jink_s = random.choice((-1, 1))
            v0 = min(exposed, key=lambda v: v['d'])
            if v0['aimed'] or v0['att']:
                by = math.atan2(v0['a']['pos'][1] - py, v0['a']['pos'][0] - px)
                cand = (math.cos(by + math.pi / 2) * self.jink_s, math.sin(by + math.pi / 2) * self.jink_s)
                if self.m.walkable_pt(px + cand[0] * 4, py + cand[1] * 4):
                    mv = cand

        # mortar shell dodge
        g = self.cfg['weapons']['mortar']['gravity']
        for pr in obs['projectiles']:
            if pr['kind'] != 'mortar':
                continue
            p0 = pr['pos']; v = pr['vel']
            zg = pz
            a = -0.5 * g; b = v[2]; c = p0[2] - zg
            disc = b * b - 4 * a * c
            if disc < 0:
                continue
            ti = (-b - math.sqrt(disc)) / (2 * a)
            if ti < 0 or ti > 4:
                continue
            ix = p0[0] + v[0] * ti; iy = p0[1] + v[1] * ti
            dd = math.hypot(ix - px, iy - py)
            if dd < 11:
                ax = px - ix; ay = py - iy; n = math.hypot(ax, ay)
                if n < 0.5:
                    ax, ay, n = -v[1], v[0], math.hypot(v[0], v[1]) or 1
                mv = (ax / n, ay / n); boost = me['energy'] > 5

        # stuck detection
        self.pos_hist.append((t, px, py))
        self.pos_hist = [p for p in self.pos_hist if t - p[0] < 1.6]
        wants = math.hypot(*mv) > 0.4
        if wants and len(self.pos_hist) > 10 and t > self.stuck_until + 1.0:
            ox, oy = self.pos_hist[0][1], self.pos_hist[0][2]
            if math.hypot(px - ox, py - oy) < 1.5 and t - self.pos_hist[0][0] > 1.4:
                self.stuck_until = t + 0.9; self.stuck_dir = random.choice((-1, 1))
                if self.goal:
                    g0 = self.goal; self.goal = None; self.path = None; self.planner = None
                    self.set_goal(g0[0], g0[1], me)
        if t < self.stuck_until and wants:
            ang = math.atan2(mv[1], mv[0]) + self.stuck_dir * 0.9
            mv = (math.cos(ang), math.sin(ang))
            if me['grounded'] and me['energy'] > 25:
                jump = True
            boost = me['energy'] > 15
        # energy reserve
        if boost and me['energy'] < 15 and not out_now:
            boost = False
        # laser charging halves speed; fine

        act['move'] = [mv[0], mv[1]]
        act['boost'] = bool(boost)
        if jump:
            act['jump'] = True

        # ---------- aiming & firing
        fire = [False, False]
        aim = None
        cur_aim = me['aim']
        if shoot:
            a = shoot['a']; tp = shoot['tc']; tv = a.get('vel', [0, 0, 0])
            d = shoot['d']
            use_laser = laser_i is not None and not shoot.get('crate') and \
                (weapons[laser_i].get('charge', 0) > 0 or weapons[laser_i]['cooldown'] < 0.4) and d < weapons[laser_i]['stats'].get('range', 280)
            if use_laser:
                pr, _ = self.solve_lead(muzzle, tp, tv, 1e6, extra=0.06)
                aim = self.aim_to(muzzle, pr)
            elif gun_i is not None:
                gs = weapons[gun_i]['stats']
                pr, _ = self.solve_lead(muzzle, tp, tv, gs.get('speed', 252))
                aim = self.aim_to(muzzle, pr)
            elif mort_i is not None:
                aim = self.aim_to(muzzle, tp)
            else:
                aim = self.aim_to(muzzle, tp)
            # error of actual aim vs desired, as lateral miss distance
            if aim:
                err_y = abs(angdiff(cur_aim[0], aim[0])); err_p = abs(cur_aim[1] - aim[1])
                miss = math.hypot(err_y, err_p) * d
                tol = 2.2 if not shoot.get('npc') and not shoot.get('crate') else 1.2
                # laser
                if laser_i is not None and not shoot.get('crate'):
                    w = weapons[laser_i]; ls = w['stats']; ch = w.get('charge', 0)
                    full = ls.get('charge', 0.75)
                    if use_laser:
                        if ch <= 0:
                            fire[laser_i] = w['cooldown'] <= 0.1 and d < ls.get('range', 280)
                        else:
                            # release only when fully charged and on target
                            fire[laser_i] = not (ch >= full * 0.97 and miss < tol)
                    elif ch > 0:
                        fire[laser_i] = not (miss < tol * 1.5)
                # gun
                if gun_i is not None:
                    w = weapons[gun_i]; gs = w['stats']
                    pr, _ = self.solve_lead(muzzle, tp, tv, gs.get('speed', 252))
                    ga = self.aim_to(muzzle, pr)
                    gmiss = math.hypot(abs(angdiff(cur_aim[0], ga[0])), abs(cur_aim[1] - ga[1])) * d
                    if gmiss < tol + 0.3 and d < gs.get('range', 230) and w.get('reload', 0) <= 0:
                        fire[gun_i] = True
                # lightning
                if lig_i is not None:
                    w = weapons[lig_i]; ls = w['stats']
                    if d < ls.get('range', 45) * 0.95 and abs(angdiff(cur_aim[0], math.atan2(tp[1] - py, tp[0] - px))) < math.radians(ls.get('cone_deg', 30)) * 0.4 \
                            and me['energy'] > 12:
                        fire[lig_i] = True
                # mortar
                if mort_i is not None and not shoot.get('crate'):
                    w = weapons[mort_i]; ms = w['stats']
                    if w['cooldown'] <= 0 and 28 < d < 220 and (gun_i is None or not fire[gun_i] or laser_i is None):
                        tof_guess = d / ms.get('speed', 72)
                        pr = [tp[0] + tv[0] * tof_guess * 1.1, tp[1] + tv[1] * tof_guess * 1.1, a['pos'][2] + 1.0]
                        tube = (px, py, pz + h_me + 0.5)
                        sol = self.ballistic(tube, pr, ms.get('speed', 72), ms.get('gravity', 22), high=not shoot['los'])
                        if sol and not fire[gun_i if gun_i is not None else 0] and not (laser_i is not None and weapons[laser_i].get('charge', 0) > 0):
                            aim = sol[0]
                            err = math.hypot(abs(angdiff(cur_aim[0], aim[0])), abs(cur_aim[1] - aim[1]))
                            if err < 0.03:
                                fire[mort_i] = True
        # mortar at tracked-but-hidden enemies (lob), when nothing else to shoot
        if not shoot and mort_i is not None and weapons[mort_i]['cooldown'] <= 0:
            for a in obs['mechs']:
                if a['kind'] != 'mech':
                    continue
                d = math.dist(a['pos'], pos)
                if 40 < d < 200 and (a['id'] in self.attackers):
                    ms = weapons[mort_i]['stats']
                    tube = (px, py, pz + h_me + 0.5)
                    sol = self.ballistic(tube, (a['pos'][0], a['pos'][1], a['pos'][2] + 1), ms.get('speed', 72), ms.get('gravity', 22), high=True)
                    if sol:
                        aim = sol[0]
                        if math.hypot(abs(angdiff(cur_aim[0], aim[0])), abs(cur_aim[1] - aim[1])) < 0.03:
                            fire[mort_i] = True
                        break
        # keep laser charge if target lost briefly: release otherwise
        if not shoot and laser_i is not None and weapons[laser_i].get('charge', 0) > 0:
            fire[laser_i] = False

        if aim is None:
            # look toward danger
            look = None
            recent_att = [v for v in self.attackers.values() if t - v[0] < 4 and v[1] is not None]
            if recent_att:
                look = max(recent_att, key=lambda v: v[0])[1]
            else:
                # tracked enemies
                tracked = [e for e in self.enemies.values() if t - e['t'] < 3]
                if tracked:
                    e = min(tracked, key=lambda e: math.dist(e['pos'], pos))
                    look = math.atan2(e['pos'][1] - py, e['pos'][0] - px)
                else:
                    snd = [s for s in self.sounds if t - s[0] < 3 and s[1] in ('gun', 'laser', 'laser_charge', 'lightning', 'mortar', 'step', 'boost', 'jet', 'reload') and s[3] != 'far']
                    if snd:
                        look = max(snd, key=lambda s: s[0])[2]
            if look is None:
                if mv != (0.0, 0.0) and not at_hide:
                    look = math.atan2(mv[1], mv[0])
                else:
                    if self.scan_dirs is None or self.scan_for != (round(px), round(py)):
                        self.scan_for = (round(px), round(py))
                        ds = []
                        for k in range(16):
                            yaw = k * TAU / 16
                            ds.append((self.m.open_dist(px, py, pz + 6, yaw, 200, 4.0), yaw))
                        ds.sort(reverse=True)
                        self.scan_dirs = [y for d, y in ds[:4] if d > 20] or [ds[0][1]]
                    i = int(t / 1.6) % len(self.scan_dirs)
                    look = self.scan_dirs[i]
            aim = [look, 0.0]
        act['aim'] = [aim[0], max(-0.69, min(1.29, aim[1]))]
        act['fire'] = fire
        # reload when idle and low
        if gun_i is not None and not fire[gun_i]:
            w = weapons[gun_i]
            if w.get('ammo', 12) < w['stats'].get('mag', 12) * 0.5 and w.get('reload', 0) <= 0 and not shoot:
                act['reload'] = True
        self.mode = mode
        return act


if __name__ == '__main__':
    mf.run(Bot)
