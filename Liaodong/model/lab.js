// ===================== 遼東 · Model Lab =====================
// The page: showroom, lineup, duel, the file, the clipping check. The soldier himself is model/rig.js (window.RIG).
(function () {
'use strict';
const $ = (id) => document.getElementById(id);
const V3 = THREE.Vector3;
const clamp = (x, a, b) => x < a ? a : x > b ? b : x, lerp = (a, b, t) => a + (b - a) * t;
const rnd = (() => { let s = 11; return () => ((s = (s * 16807) % 2147483647) / 2147483647); })();
const { analyse, Man, ARMOR, WEAPON, CHAINS, SPEED, TRAVEL } = window.RIG; let BODY = null;
// ---------------------------------------------------------------------------------------------------------------------
// the scene, the modes, the controls
// ---------------------------------------------------------------------------------------------------------------------
const Qs = new URLSearchParams(location.search);
const renderer = new THREE.WebGLRenderer({ canvas: $('c'), antialias: true, preserveDrawingBuffer: Qs.has('shot') });
renderer.setPixelRatio(Math.min(2, window.devicePixelRatio || 1)); renderer.outputEncoding = THREE.sRGBEncoding; renderer.toneMapping = THREE.ACESFilmicToneMapping; renderer.toneMappingExposure = 1.05;
renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
const scene = new THREE.Scene(); scene.background = new THREE.Color(0xd8ccb0); scene.fog = new THREE.Fog(0xd8ccb0, 16, 60); /* a paper sky, the far field fading into it like ink on xuan paper */
const camera = new THREE.PerspectiveCamera(36, 1, 0.05, 200); camera.position.set(1.6, 1.55, 3.8);
const orbit = new THREE.OrbitControls(camera, renderer.domElement); orbit.target.set(0, 1.05, 0); orbit.enableDamping = true; orbit.minDistance = 0.8; orbit.maxDistance = 30; orbit.maxPolarAngle = 1.52;
scene.add(new THREE.HemisphereLight(0xf0e6d0, 0x4a3f30, 0.75));
{ // something for metal to reflect: a sky over warm earth, prefiltered once
  const es = new THREE.Scene(), geo = new THREE.SphereGeometry(10, 32, 16), col = []; const P = geo.attributes.position, top = new THREE.Color(0xe8eef6), hor = new THREE.Color(0xf2e6cc), low = new THREE.Color(0x4a3c2c), c = new THREE.Color();
  for (let i = 0; i < P.count; i++) { const y = P.getY(i) / 10; if (y > 0) c.copy(hor).lerp(top, Math.pow(y, 0.6)); else c.copy(hor).lerp(low, Math.min(1, -y * 3)); col.push(c.r, c.g, c.b); }
  geo.setAttribute('color', new THREE.Float32BufferAttribute(col, 3)); es.add(new THREE.Mesh(geo, new THREE.MeshBasicMaterial({ vertexColors: true, side: THREE.BackSide })));
  const sunDisc = new THREE.Mesh(new THREE.SphereGeometry(0.8, 12, 8), new THREE.MeshBasicMaterial({ color: 0xfff4e0 })); sunDisc.position.set(5, 7, 6); es.add(sunDisc);
  const pm = new THREE.PMREMGenerator(renderer); scene.environment = pm.fromScene(es, 0.02).texture; pm.dispose(); }
const sun = new THREE.DirectionalLight(0xffe2b8, 1.9); sun.position.set(5, 9, 6); sun.castShadow = true; sun.shadow.mapSize.set(2048, 2048); const sc = sun.shadow.camera; sc.left = -9; sc.right = 9; sc.top = 9; sc.bottom = -9; sc.near = 1; sc.far = 40; sun.shadow.bias = -0.0004; sun.shadow.normalBias = 0.02; scene.add(sun); scene.add(sun.target);
{ const c = document.createElement('canvas'); c.width = c.height = 512; const g = c.getContext('2d'); g.fillStyle = '#a89878'; g.fillRect(0, 0, 512, 512); for (let i = 0; i < 9000; i++) { const r = rnd(); g.fillStyle = r < 0.33 ? 'rgba(90,84,58,.12)' : r < 0.66 ? 'rgba(150,132,100,.14)' : 'rgba(60,50,36,.1)'; const sz = 8 + rnd() * 16; g.fillRect(((rnd() * 64) | 0) * 8, ((rnd() * 64) | 0) * 8, sz, sz); } /* trampled earth in squared patches, to sit with the blocks */
  const t = new THREE.CanvasTexture(c); t.wrapS = t.wrapT = THREE.RepeatWrapping; t.repeat.set(30, 30); t.encoding = THREE.sRGBEncoding; t.anisotropy = 8;
  const gr = new THREE.Mesh(new THREE.PlaneGeometry(160, 160), new THREE.MeshStandardMaterial({ map: t, roughness: 1 })); gr.rotation.x = -Math.PI / 2; gr.receiveShadow = true; scene.add(gr); }
let men = [], mode = 'show', sel = null, cur = { set: Qs.get('set') || 'ming_studded', wpn: Qs.get('wpn') || 'dao' }, duel = null, file = null, check = null, T = 0;
// a man's feet: where he goes and which way he faces; the animator gets his speed and the angle of travel off his facing
function mover(m, x, z, yaw) { m.root.position.set(x, 0, z); m.root.rotation.y = yaw; m.mv = { x, z, yaw, vx: 0, vz: 0, path: null, face: null }; }
function stepMover(m, dt) {
  const v = m.mv; if (!v) return; let vx = 0, vz = 0;
  if (v.path) { const P = v.path; P.a += P.w * dt; const nx = P.cx + Math.sin(P.a) * P.r, nz = P.cz + Math.cos(P.a) * P.r; vx = (nx - v.x) / dt; vz = (nz - v.z) / dt; v.x = nx; v.z = nz;
    const fy = P.face === 'center' ? Math.atan2(P.cx - v.x, P.cz - v.z) : P.face === 'back' ? Math.atan2(-vx, -vz) : Math.atan2(vx, vz); v.yaw = turnTo(v.yaw, fy, dt * 6); }
  else if (v.to) { const dx = v.to.x - v.x, dz = v.to.z - v.z, d = Math.hypot(dx, dz); if (d < 0.05) { v.to = null; } else { const s = Math.min(v.to.speed, d * 4); vx = dx / d * s; vz = dz / d * s; v.x += vx * dt; v.z += vz * dt; } if (v.face !== null && v.face !== undefined) v.yaw = turnTo(v.yaw, v.face, dt * 7); else if (d > 0.3 && !v.to?.keepFace) v.yaw = turnTo(v.yaw, Math.atan2(vx, vz), dt * 6); }
  else if (v.face !== null && v.face !== undefined) v.yaw = turnTo(v.yaw, v.face, dt * 7);
  m.root.position.set(v.x, 0, v.z); m.root.rotation.y = v.yaw;
  { const o = m.anim.one, tr = o && TRAVEL[o.name]; if (tr && o.a.time < o.a.getClip().duration - 0.05) { const d = o.a.getClip().duration, k = Math.sin(clamp(o.a.time / d, 0, 1) * Math.PI) * Math.PI / 2 / d; /* the root motion of a dodge, roll or dash: most of it in the middle of the move */
      const lx = Math.cos(v.yaw), lz = -Math.sin(v.yaw), fx = Math.sin(v.yaw), fz = Math.cos(v.yaw); v.x += (lx * tr[0] + fx * tr[1]) * k * dt; v.z += (lz * tr[0] + fz * tr[1]) * k * dt; m.root.position.set(v.x, 0, v.z); } }
  const sp = Math.hypot(vx, vz); v.sp = lerp(v.sp || 0, sp, Math.min(1, dt * 8)); m.anim.speed = v.sp; if (sp > 0.05) { const fx = Math.sin(v.yaw), fz = Math.cos(v.yaw), lx = Math.cos(v.yaw), lz = -Math.sin(v.yaw); m.anim.ang = Math.atan2(vx * lx + vz * lz, vx * fx + vz * fz); }
}
function turnTo(a, b, k) { let d = b - a; while (d > Math.PI) d -= 2 * Math.PI; while (d < -Math.PI) d += 2 * Math.PI; return a + d * Math.min(1, k); }
function clear() { for (const m of men) m.dispose(); men = []; sel = null; duel = null; file = null; check = null; if (crowd) { crowd.C.dispose(); crowd = null; } }
function setMode(mm) {
  mode = mm; clear(); for (const b of document.querySelectorAll('#modes button')) b.classList.toggle('on', b.dataset.m === mm);
  if (mm === 'show' || mm === 'check') { const m = new Man(cur.set, cur.wpn, scene); mover(m, 0, 0, 0); men.push(m); sel = m; camera.position.set(1.5, 1.5, 3.6); orbit.target.set(0, 1.0, 0); if (mm === 'check') startCheck(); }
  if (mm === 'lineup') { const keys = Object.keys(ARMOR).filter(k => k !== 'bare'), W = ['dao', 'spear', 'shield', 'dao', 'dao', 'spear', 'bow', 'dao']; keys.forEach((k, i) => { const m = new Man(k, W[i % W.length], scene); mover(m, (i - (keys.length - 1) / 2) * 1.3, 0, 0); men.push(m); }); sel = men[0]; camera.position.set(0, 2.2, 9.5); orbit.target.set(0, 1.0, 0); }
  if (mm === 'duel') startDuel();
  if (mm === 'file') startFile();
  if (mm === 'crowd') startCrowd();
  buildSide(); buildActs();
}
// ---- the duel: two men at measure, a step in with a chain, a guard or a hit taken on the side the blade came from, until one falls
const STRIKE = { Sword_Regular_A: 'R', Sword_Regular_B: 'L', Sword_Regular_C: 'U', Sword_Light_A: 'R', Sword_Light_B: 'L', Sword_Light_C: 'D', Sword_Heavy_A: 'U', Sword_Heavy_B: 'R', Sword_Light_Combo: 'L', Sword_UpperCut: 'D', Sword_Dash: 'R' };
function startDuel() { const a = new Man(Qs.get('a') || 'ming_lamellar', 'dao', scene), b = new Man(Qs.get('b') || 'jin_yellow', 'dao', scene); mover(a, -1.3, 0, Math.PI / 2); mover(b, 1.3, 0, -Math.PI / 2); men.push(a, b); sel = a;
  for (const [m, o] of [[a, b], [b, a]]) { m.foe = o; m.hp = 4; m.anim.combat = true; m.anim.keepCombat = true; m.ai = { t: 0.6 + Math.random(), st: 'measure', orbit: Math.random() < 0.5 ? 1 : -1 }; }
  duel = { t: 0, over: 0 }; camera.position.set(0.4, 2.0, 5.2); orbit.target.set(0, 1.0, 0); }
function duelThink(dt) {
  if (!duel) return; duel.t += dt;
  if (duel.over) { duel.over -= dt; if (duel.over <= 0) setMode('duel'); return; }
  for (const m of men) { const o = m.foe, v = m.mv, A = m.anim; if (A.dead || A.down) continue; A.look = o.root.position.clone().add(new V3(0, 1.6, 0));
    const dx = o.mv.x - v.x, dz = o.mv.z - v.z, d = Math.hypot(dx, dz), face = Math.atan2(dx, dz); v.face = face; const ai = m.ai; ai.t -= dt;
    if (A.one && A.one.attack) { v.to = null; // the blade lands about two fifths into the clip: the other man has guarded or he is hit on that side
      const p = A.one.a.time / A.one.a.getClip().duration; if (!A.one.landed && p > 0.4) { A.one.landed = true; if (d < 1.9 && !o.anim.dead) { if (o.anim.blockOn) { spark(o); } else { o.hp--; o.setGrime(o.grime.uDust.value + 0.1, o.grime.uMud.value + 0.05, o.grime.uBlood.value + 0.25); /* every blow taken shows */ o.anim.hit(STRIKE[A.one.name] || 'F', A.one.name.includes('Heavy') && o.hp <= 1); if (o.hp <= 0) setTimeout(() => { o.anim.die(); m.anim.keepCombat = false; duel.over = 6; setTimeout(() => { if (!m.anim.dead) m.anim.play('Celebration', { fade: 0.3, expr: 'shout' }); }, 1500); }, 250); } } } continue; }
    if (o.anim.one && o.anim.one.attack && d < 2.2 && !A.blockOn && !A.one && Math.random() < 0.06) { A.block(true); ai.unblock = 0.55; }
    if (ai.unblock !== undefined) { ai.unblock -= dt; if (ai.unblock <= 0) { A.block(false); ai.unblock = undefined; } continue; }
    if (A.one) continue;
    if (ai.st === 'measure') { const want = 2.5; const k = d - want; const side = ai.orbit, lx = Math.cos(face), lz = -Math.sin(face);
      v.to = { x: v.x + dx / d * k * 0.6 + lx * side * 0.5, z: v.z + dz / d * k * 0.6 + lz * side * 0.5, speed: 0.9, keepFace: true }; if (ai.t <= 0) { ai.st = 'close'; ai.t = 1.4; } if (Math.random() < 0.01) ai.orbit = -ai.orbit; }
    else if (ai.st === 'close') { v.to = { x: o.mv.x - dx / d * 1.45, z: o.mv.z - dz / d * 1.45, speed: 2.4, keepFace: true }; if (d < 1.7 || ai.t <= 0) { const keys = ['lianhuan', 'duanda', 'po', 'zhui', 'chong']; const k = keys[(Math.random() * keys.length) | 0]; A.attack(k); if (k !== 'zhui' && k !== 'chong') { ai.more = (Math.random() * 3) | 0; } ai.st = 'press'; ai.t = 0.5; } }
    else if (ai.st === 'press') { if (ai.more > 0 && A.chain) { A.attack(A.chain); ai.more--; } else { ai.st = 'measure'; ai.t = 1.2 + Math.random() * 2; } }
  }
}
function spark(m) { const s = new THREE.PointLight(0xffd080, 2.5, 2); s.position.copy(m.bones.hand_r.getWorldPosition(new V3())); scene.add(s); setTimeout(() => scene.remove(s), 90); }
// ---- the file: ten men march, halt, make ready and strike together, and fall back facing the enemy
function startFile() { const S = ['ming_studded', 'ming_jacket', 'ming_lamellar', 'ming_studded', 'qi_rattan'], W = ['spear', 'spear', 'dao', 'spear', 'shield'];
  for (let r = 0; r < 2; r++) for (let i = 0; i < 5; i++) { const m = new Man(S[(i + r * 2) % S.length], r === 0 ? W[i] : 'spear', scene); mover(m, (i - 2) * 1.15, -6 - r * 1.4, 0); m.anim.keepCombat = false; men.push(m); }
  file = { t: 0, st: 'march' }; sel = men[2]; camera.position.set(6, 3, 6); orbit.target.set(0, 1, 0); }
function fileThink(dt) { if (!file) return; file.t += dt; const F = file;
  if (F.st === 'march') { for (const m of men) { m.mv.to = { x: m.mv.x, z: m.mv.z + 2, speed: 1.4 }; m.mv.face = 0; } if (men[0].mv.z > 2) { F.st = 'ready'; F.t = 0; for (const m of men) { m.mv.to = null; m.anim.combat = true; } } }
  else if (F.st === 'ready') { if (F.t > 1.5 && !F.struck) { F.struck = true; men.forEach((m, i) => setTimeout(() => m.anim.attack('lianhuan'), i * 60 + Math.random() * 120)); } if (F.t > 4.2) { F.st = 'back'; F.t = 0; F.struck = false; } }
  else if (F.st === 'back') { for (const m of men) { m.mv.to = { x: m.mv.x, z: m.mv.z - 2, speed: 1.1, keepFace: true }; m.mv.face = 0; } if (men[0].mv.z < -6) { F.st = 'march'; F.t = 0; for (const m of men) m.anim.combat = false; } } }
// ---- the crowd: two armies on the baked poses (rig.js Crowd), every man a few numbers, posed on the graphics card
let crowd = null;
function startCrowd() { const C = new RIG.Crowd(scene, 220), M = [];
  const ming = ['ming_studded', 'ming_jacket', 'ming_studded', 'ming_robe', 'ming_mail', 'qi_rattan'], jin = ['jin_yellow', 'jin_white', 'jin_blue_b', 'jin_red'];
  for (const side of [0, 1]) for (let r = 0; r < 8; r++) for (let c = 0; c < 20; c++) { const set = side ? jin[(c / 5 | 0) % 4] : ming[(r * 3 + c) % ming.length], wpn = side ? (r < 3 ? 'spear' : r < 6 ? 'dao' : 'bow') : set === 'qi_rattan' ? 'shield' : r < 2 ? 'spear' : r < 5 ? 'dao' : 'gun';
    const x = (c - 9.5) * 1.15 + (rnd() - 0.5) * 0.2, z = (side ? 1 : -1) * (14 + r * 1.3), F = RIG.crowdState(wpn); F.seed = rnd(); M.push({ set, wpn, x, z, yaw: side ? Math.PI : 0, side, F, hp: 3, cd: 1 + rnd() * 3, ctl: {} }); }
  crowd = { C, M, t: 0 }; camera.position.set(16, 7, 22); orbit.target.set(0, 1, 0); }
function crowdThink(dt) { if (!crowd) return; crowd.t += dt; const { C, M } = crowd;
  for (const u of M) { const c = u.ctl; c.hit = null; c.release = false; c.kick = false; if (u.hp <= 0) { c.dead = true; continue; }
    const front = u.side ? 1.0 : -1.0, stop = front * (0.9 + (Math.abs(u.z) - 14) * 0) ; const want = u.side ? 0.95 + (u.r0 = u.r0 || (Math.abs(u.z) - 14)) : -0.95 - (u.r0 = u.r0 || (Math.abs(u.z) - 14));
    const dz = want - u.z, sp = Math.abs(dz) > 0.1 ? Math.min(u.wpn === 'bow' || u.wpn === 'gun' ? 1.3 : 2.8, Math.abs(dz) * 2) : 0; u.z += Math.sign(dz) * sp * dt; c.speed = sp; c.ang = 0; c.combat = crowd.t > 4;
    const engaged = Math.abs(u.z) < 2.6 + 0.1; u.cd -= dt;
    if ((u.wpn === 'gun' || u.wpn === 'bow') && crowd.t > 6) { c.aim = (crowd.t + u.F.seed * 5) % 5 < 3; }
    if (engaged && u.cd <= 0) { u.cd = 1.4 + rnd() * 2.2; c.windup = (c.windup || 0) + 1; c.dir = 'RLUD'[(rnd() * 4) | 0]; c.wd = 0.3 + rnd() * 0.4; if (u.wpn === 'spear') c.release = true;
      const foes = M.filter(o => o.side !== u.side && o.hp > 0 && Math.abs(o.x - u.x) < 1.4 && Math.abs(o.z) < 2.8); const o = foes[(rnd() * foes.length) | 0]; if (o && rnd() < 0.5) setTimeout(() => { if (o.ctl.block) return; o.hp--; o.ctl.hit = 'LRUF'[(rnd() * 4) | 0]; }, 300); }
    c.block = engaged && (crowd.t * 0.7 + u.F.seed * 9) % 4 < 0.9; c.downed = false; }
  C.begin(); for (const u of M) { RIG.crowdStep(u.F, dt, u.ctl); u.ctl.hit = null; C.add(u.set, u.wpn, u.x, 0, u.z, u.yaw, u.F); } C.end(); }
// ---- the clipping check: the covered body drawn over the armor in pure red, only where it would be seen in front of it
const RED = new THREE.MeshBasicMaterial({ color: 0xff0000, skinning: true, toneMapped: false, fog: false });
function overlay(m, on) { if (m.red) { m.red.parent.remove(m.red); m.red = null; } if (!on || !m.hidGeo) return;
  const r = new THREE.SkinnedMesh(m.hidGeo, RED); r.bind(m.skel, m.body[0].bindMatrix); r.renderOrder = 10; r.frustumCulled = false; m.host.add(r); m.red = r; }
const CLIPS = () => Object.keys(BODY.clips).filter(n => n !== 'A_TPose').sort();
function startCheck() { check = { i: 0, t: 0, res: null }; overlay(men[0], true); playClip(men[0], CLIPS()[0], true); }
function playClip(m, name, loop) { m.anim.revive(); m.anim.play(name, { fade: 0.15, once: !loop, clamp: true, then: loop ? null : () => {} }); if (loop) { m.anim.one.a.setLoop(THREE.LoopRepeat, Infinity); m.anim.one.hold = true; } m.clipName = name; }
function countRed() { const gl = renderer.getContext(), W = gl.drawingBufferWidth, H = gl.drawingBufferHeight, px = new Uint8Array(W * H * 4); gl.readPixels(0, 0, W, H, gl.RGBA, gl.UNSIGNED_BYTE, px); let n = 0; for (let i = 0; i < px.length; i += 4) if (px[i] > 200 && px[i + 1] < 40 && px[i + 2] < 40) n++; return n; }
function measureAll(setKey, views) { // every clip, eight moments each, from several sides: how many red pixels ever show
  const m = men[0], res = { worst: 0, worstAt: '', total: 0, frames: 0, sets: {} }; const keys = setKey ? [setKey] : Object.keys(ARMOR).filter(k => k !== 'bare'); const cams = views || [[0, 1.4, 3.4], [3.0, 1.6, 1.2], [-2.6, 2.4, -2.2], [0.6, 0.6, 2.6]];
  for (const k of keys) { m.equip(k); overlay(m, true); let worst = 0, at = '';
    for (const name of CLIPS()) { const c = BODY.clips[name]; m.mixer.stopAllAction(); const a = m.mixer.clipAction(c); a.reset().setLoop(THREE.LoopRepeat, Infinity).setEffectiveWeight(1).play();
      for (let i = 0; i < 8; i++) { m.mixer.setTime(c.duration * i / 8); m.root.updateMatrixWorld(true); for (const cp of cams) { camera.position.set(cp[0], cp[1], cp[2]); camera.lookAt(0, 0.9, 0); renderer.render(scene, camera); const n = countRed(); res.total += n; res.frames++; if (n > worst) { worst = n; at = name + '@' + i + '/8 view' + cams.indexOf(cp); } } } }
    res.sets[k] = { worst, at }; if (worst > res.worst) { res.worst = worst; res.worstAt = k + ' ' + at; } }
  m.equip(cur.set); overlay(m, true); m.mixer.stopAllAction(); m.anim.one = null; m.anim.os = []; m.anim.bw = {}; camera.position.set(1.5, 1.5, 3.6); orbit.target.set(0, 1.0, 0); return res;
}
// ---- the side panel and the action bar
function buildSide() {
  const target = () => (mode === 'lineup' && sel ? [sel] : mode === 'duel' || mode === 'file' ? [] : men);
  $('armors').innerHTML = Object.entries(ARMOR).map(([k, a]) => `<button data-k="${k}" class="${(sel ? sel.setKey : cur.set) === k ? 'on' : ''}">${a.name}<small>${a.en}</small></button>`).join('');
  $('armors').onclick = (e) => { const b = e.target.closest('button'); if (!b) return; cur.set = b.dataset.k; for (const m of target()) { m.equip(cur.set); if (mode === 'check') overlay(m, true); } buildSide(); };
  $('weapons').innerHTML = Object.entries(WEAPON).map(([k, w]) => `<button data-k="${k}" class="${(sel ? sel.wpnKey : cur.wpn) === k ? 'on' : ''}">${w.name}</button>`).join('');
  $('weapons').onclick = (e) => { const b = e.target.closest('button'); if (!b) return; cur.wpn = b.dataset.k; for (const m of target()) m.arm(cur.wpn); buildSide(); };
  $('cliplist').innerHTML = CLIPS().map(n => `<button data-k="${n}">${n.replace(/_/g, ' ')}</button>`).join('');
  $('cliplist').onclick = (e) => { const b = e.target.closest('button'); if (!b) return; for (const m of (sel ? [sel] : men)) playClip(m, b.dataset.k, /Loop/.test(b.dataset.k)); if (check) check.i = CLIPS().indexOf(b.dataset.k); };
}
function buildActs() {
  const box = $('acts'); const S = () => (sel ? [sel] : men); const each = (f) => () => { for (const m of S()) f(m); };
  const go = (path) => each(m => { m.anim.revive(); m.mv.to = null; m.mv.face = null; m.mv.path = path ? Object.assign({ cx: m.mv.x - Math.sin(m.mv.yaw + Math.PI / 2) * 2.4, cz: m.mv.z - Math.cos(m.mv.yaw + Math.PI / 2) * 2.4, r: 2.4, a: m.mv.yaw + Math.PI / 2 }, path) : null; if (!path) m.mv.face = m.mv.yaw; });
  const A = [
    ['Stand', go(null)], ['Walk', go({ w: 0.55, face: 'path' })], ['Jog', go({ w: 1.35, face: 'path' })], ['Sprint', go({ w: 2.3, face: 'path' })], ['Circle (strafe)', go({ w: 0.5, face: 'center' })], ['Back away', go({ w: 0.5, face: 'back' })], 0,
    ...Object.entries(CHAINS).map(([k, c]) => [c.zh + ' ' + c.en.split(',')[0], each(m => m.anim.attack(k))]), ['Block', null, 'hold'], 0,
    ['Hit · left', each(m => m.anim.hit('L'))], ['Hit · right', each(m => m.anim.hit('R'))], ['Hit · overhead', each(m => m.anim.hit('U'))], ['Hit · thrust', each(m => m.anim.hit('D'))], ['Knocked back', each(m => m.anim.hit('F', true))], 0,
    ['Dodge left', each(m => m.anim.play('Dodge_Left'))], ['Dodge right', each(m => m.anim.play('Dodge_Right'))], ['Roll', each(m => m.anim.play('Roll'))], ['Kick', each(m => m.anim.play('Kick', { expr: 'shout' }))], ['Shield shove', each(m => m.anim.play('Shield_OneShot', { expr: 'shout' }))], 0,
    ['Bow: draw', each(m => m.anim.play('Bow_Notch', { then: () => { m.anim.hold = 'Bow_Aim_Neutral'; } }))], ['Bow: loose', each(m => { m.anim.hold = null; m.anim.play('Bow_Shoot'); })], 0,
    ['Wounded', each(m => m.anim.wound())], ['Help up', each(m => helpUp(m))], ['Bandage', each(m => { m.anim.revive(); m.anim.hold = 'Bandage_Loop'; })], ['Die', each(m => m.anim.die())], ['Revive', each(m => m.anim.revive())], ['Cheer', each(m => m.anim.play('Celebration', { expr: 'shout' }))], 0,
    ['Order: charge! (point)', each(m => { const f = new V3(Math.sin(m.mv.yaw + 0.35), 0, Math.cos(m.mv.yaw + 0.35)); m.anim.order(m.root.position.clone().add(f.multiplyScalar(8)).add(new V3(0, 0.5, 0)), 2.4); })], ['Look at me', each(m => { m.anim.look = m.anim.look ? null : camera.position; })], ['Combat stance', each(m => { m.anim.combat = !m.anim.combat; m.anim.keepCombat = m.anim.combat; })], 0, ['Grime on / off', () => { RIG.GRIME.uOn.value = RIG.GRIME.uOn.value ? 0 : 1; }], ['Grime: fresh', each(m => m.setGrime(0.05, 0, 0))], ['Grime: on campaign', each(m => m.setGrime(0.45, 0.35, 0))], ['Grime: after the battle', each(m => m.setGrime(0.85, 0.8, 0.7))],
  ];
  if (mode === 'check') A.unshift(['Measure every set', () => { $('stats').textContent = 'measuring…'; setTimeout(() => { const r = measureAll(); $('stats').textContent = 'red pixels (covered skin\nin front of its armor)\nworst ' + r.worst + '\n' + Object.entries(r.sets).map(([k, v]) => k.padEnd(14) + String(v.worst).padStart(6)).join('\n'); window.LAB.lastMeasure = r; }, 30); }], 0);
  box.innerHTML = ''; for (const a of A) { if (!a) { const s = document.createElement('span'); s.className = 'sep'; box.appendChild(s); continue; } const b = document.createElement('button'); b.textContent = a[0];
    if (a[2] === 'hold') { b.onpointerdown = () => { for (const m of S()) m.anim.block(true); }; b.onpointerup = b.onpointerleave = () => { for (const m of S()) m.anim.block(false); }; } else b.onclick = a[1]; box.appendChild(b); }
}
function helpUp(m) { // a comrade comes, kneels, takes him under the arm, and they rise together
  if (!m.anim.down) m.anim.wound(); const h = new Man('ming_jacket', 'none', scene); const yaw = m.mv.yaw; mover(h, m.mv.x + Math.sin(yaw + 1.2) * 3, m.mv.z + Math.cos(yaw + 1.2) * 3, 0); men.push(h);
  const spot = { x: m.mv.x + Math.sin(yaw + Math.PI / 2) * 0.75, z: m.mv.z + Math.cos(yaw + Math.PI / 2) * 0.75 };
  h.mv.to = { x: spot.x, z: spot.z, speed: 2.6 }; h.anim.look = m.root.position.clone().add(new V3(0, 0.3, 0));
  const wait = setInterval(() => { if (!h.mv.to) { clearInterval(wait); h.mv.face = Math.atan2(m.mv.x - h.mv.x, m.mv.z - h.mv.z); h.anim.play('PickUp_Kneeling', { fade: 0.2, then: () => { h.anim.play('Yes'); } }); setTimeout(() => m.anim.rise(), 700); } }, 50);
}
// ---- picking a man in the lineup: the nearest pelvis on screen
renderer.domElement.addEventListener('click', (e) => { if (mode !== 'lineup') return; const r = renderer.domElement.getBoundingClientRect(), x = (e.clientX - r.left) / r.width * 2 - 1, y = -(e.clientY - r.top) / r.height * 2 + 1; let best = null, bd = 0.15;
  for (const m of men) { const p = m.bones.spine_02.getWorldPosition(new V3()).project(camera); const d = Math.hypot(p.x - x, p.y - y); if (d < bd) { bd = d; best = m; } } if (best) { sel = best; buildSide(); } });
document.getElementById('modes').onclick = (e) => { const b = e.target.closest('button'); if (b) setMode(b.dataset.m); };
function resize() { const w = window.innerWidth, h = window.innerHeight; renderer.setSize(w, h, false); camera.aspect = w / h; camera.updateProjectionMatrix(); } window.addEventListener('resize', resize);
let last = performance.now(), fpsA = 60;
function frame(now) {
  const dt = Math.min(0.05, (now - last) / 1000); last = now; T += dt; fpsA = lerp(fpsA, 1 / Math.max(dt, 0.001), 0.05);
  duelThink(dt); fileThink(dt); crowdThink(dt);
  if (check && !check.pause) { check.t += dt; const m = men[0], name = m.clipName, c = BODY.clips[name]; if (c && check.t > Math.max(2.4, c.duration * 2)) { check.t = 0; check.i = (check.i + 1) % CLIPS().length; playClip(m, CLIPS()[check.i], true); } }
  for (const m of men) { stepMover(m, dt); m.update(dt); }
  if (mode === 'show' && men[0]) { const p = men[0].root.position; orbit.target.lerp(new V3(p.x, 1.0, p.z), Math.min(1, dt * 3)); }
  sun.position.set(orbit.target.x + 5, 9, orbit.target.z + 6); sun.target.position.copy(orbit.target);
  orbit.update(); renderer.render(scene, camera);
  if (!window.LAB.lastMeasure || mode !== 'check') { const info = renderer.info.render, s = sel || men[0]; $('stats').textContent = `fps ${fpsA.toFixed(0)}\ndraw calls ${info.calls}\ntriangles ${(info.triangles / 1000).toFixed(1)}k\nmen ${men.length + (crowd ? crowd.M.length : 0)}\n` + (s ? `\n${ARMOR[s.setKey].name}\n${WEAPON[s.wpnKey].name}\nclip ${s.anim.one ? s.anim.one.name : s.anim.base || ''}${s.anim.chain ? '\nchain ' + CHAINS[s.anim.chain].zh + ' ' + (s.anim.step + 1) + '/' + CHAINS[s.anim.chain].steps.length : ''}` : ''); }
  if (!Qs.has('noloop')) requestAnimationFrame(frame);
}
window.LAB = { get BODY() { return BODY; }, setMode, measureAll, get men() { return men; }, renderer, scene, camera, orbit, ARMOR, WEAPON, CHAINS, SPEED, step: (dt) => { for (const m of men) { stepMover(m, dt); m.update(dt); } duelThink(dt); fileThink(dt); crowdThink(dt); orbit.update(); renderer.render(scene, camera); }, countRed, overlay };
new THREE.GLTFLoader().load('man.glb', (g) => {
  BODY = analyse(g); resize(); setMode(Qs.get('mode') || 'show'); $('load').remove(); window.LAB.ready = true; requestAnimationFrame((t) => { last = t; frame(t); });
}, undefined, (err) => { $('load').textContent = 'could not load the model: ' + (err && err.message || err); window.LAB.error = String(err && err.message || err); });
})();
