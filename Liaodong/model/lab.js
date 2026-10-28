// ===================== 遼東 · Model Lab =====================
// An experiment toward a new figure for the game: one rigged human (Quaternius's Universal Animation Library mannequin, CC0:
// 65 bones with fingers, 80 clips cut from its two libraries by model/build_glb.mjs) that *wears* armor instead of every kind of
// soldier being a model of its own.
//
// The armor cannot clip, by construction. Every plate, coat, sleeve, boot and glove is grown from the body's own surface: the
// triangles of the body under it are copied, pushed outward along the (welded) normals by the piece's thickness, and keep the
// body's exact bone weights. Skinning moves a plate point exactly as it moves the skin point under it, so the plate stays the
// same distance outside the skin in every pose. Layers stack by thickness (shirt < coat < plates), and the body under a piece
// is not drawn at all. Helmets and weapons are rigid on one bone (the head, a hand, a forearm), sized from that bone's own
// vertices with a margin. The "Clipping check" mode paints any covered body point that comes in front of its armor red.
(function () {
'use strict';
const $ = (id) => document.getElementById(id);
const V3 = THREE.Vector3, Q = THREE.Quaternion, M4 = THREE.Matrix4;
const GETK = ['getX', 'getY', 'getZ', 'getW'], comp = (a, i, k) => a[GETK[k]](i); /* r128 attributes (interleaved ones too) have getX..getW but no getComponent */
const clamp = (x, a, b) => x < a ? a : x > b ? b : x, lerp = (a, b, t) => a + (b - a) * t, sm = (t) => t * t * (3 - 2 * t);
const rnd = (() => { let s = 7; return () => ((s = (s * 16807) % 2147483647) / 2147483647); })(); // a fixed stream: the same textures every load

// ---------------------------------------------------------------------------------------------------------------------
// textures: drawn tiles with a height field turned into a normal map, so lamellae, studs and quilting have relief in light
// ---------------------------------------------------------------------------------------------------------------------
const TEX = {};
function heightToNormal(hc, strength) {
  const W = hc.width, H = hc.height, src = hc.getContext('2d').getImageData(0, 0, W, H).data;
  const out = document.createElement('canvas'); out.width = W; out.height = H; const g = out.getContext('2d'), img = g.createImageData(W, H), d = img.data;
  const h = (x, y) => src[(((y + H) % H) * W + ((x + W) % W)) * 4] / 255;
  for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
    const dx = (h(x + 1, y) - h(x - 1, y)) * strength, dy = (h(x, y + 1) - h(x, y - 1)) * strength; const l = Math.hypot(dx, dy, 1);
    const i = (y * W + x) * 4; d[i] = (-dx / l * 0.5 + 0.5) * 255; d[i + 1] = (dy / l * 0.5 + 0.5) * 255; d[i + 2] = (1 / l * 0.5 + 0.5) * 255; d[i + 3] = 255; }
  g.putImageData(img, 0, 0); return out;
}
function canvasPair(W, H) { const c = document.createElement('canvas'); c.width = W; c.height = H; const hc = document.createElement('canvas'); hc.width = W; hc.height = H; const hg = hc.getContext('2d'); hg.fillStyle = '#000'; hg.fillRect(0, 0, W, H); return [c, c.getContext('2d'), hc, hg]; }
function rr(g, x, y, w, h, r) { g.beginPath(); g.moveTo(x + r, y); g.arcTo(x + w, y, x + w, y + h, r); g.arcTo(x + w, y + h, x, y + h, r); g.arcTo(x, y + h, x, y, r); g.arcTo(x, y, x + w, y, r); g.closePath(); }
function noiseOver(g, W, H, a, n) { for (let i = 0; i < (n || 2600); i++) { g.fillStyle = `rgba(${rnd() < 0.5 ? '0,0,0' : '255,255,255'},${a * rnd()})`; g.fillRect(rnd() * W, rnd() * H, 1 + rnd() * 2, 1 + rnd() * 2); } }
// a pattern: { map, normalMap, rough, metal, tile:[metres wide, metres tall] }
function pattern(kind, col, col2) {
  const key = kind + col + (col2 || ''); if (TEX[key]) return TEX[key];
  const W = 256, H = 256; const [c, g, hc, hg] = canvasPair(W, H); let tile = [0.16, 0.16], rough = 0.8, metal = 0, str = 3;
  if (kind === 'lamellar') { // 札甲: rows of narrow plates, each overlapping the next, laced through at top and middle
    tile = [0.165, 0.2]; rough = 0.5; metal = 0.45; str = 2.2; const cols = 6, rows = 3, pw = W / cols, ph = H / rows;
    g.fillStyle = col2 || '#5a1a14'; g.fillRect(0, 0, W, H);
    for (let r = 0; r < rows; r++) for (let k = -1; k <= cols; k++) { const x = k * pw + (r % 2 ? pw / 2 : 0), y = r * ph;
      const grd = g.createLinearGradient(x, 0, x + pw, 0); grd.addColorStop(0, shade(col, -0.2)); grd.addColorStop(0.5, shade(col, 0.1)); grd.addColorStop(1, shade(col, -0.25)); g.fillStyle = grd; rr(g, x + 1.5, y + 2, pw - 3, ph * 1.04, pw * 0.45); g.fill();
      g.strokeStyle = 'rgba(0,0,0,.55)'; g.lineWidth = 1.2; g.stroke();
      const hgd = hg.createLinearGradient(x, 0, x + pw, 0); hgd.addColorStop(0, '#333'); hgd.addColorStop(0.5, '#fff'); hgd.addColorStop(1, '#333'); hg.fillStyle = hgd; rr(hg, x + 1.5, y + 2, pw - 3, ph * 1.04, pw * 0.45); hg.fill();
      g.fillStyle = col2 || '#7a1e16'; for (const yy of [y + ph * 0.22, y + ph * 0.6]) { g.fillRect(x + pw * 0.3, yy, pw * 0.4, 3.2); hg.fillStyle = '#888'; hg.fillRect(x + pw * 0.3, yy, pw * 0.4, 3.2); } }
  } else if (kind === 'studs') { // 布面甲 / 棉甲: cloth over iron, the plates riveted through with brass studs in rows
    tile = [0.26, 0.26]; rough = 0.82; metal = 0.25; str = 6; g.fillStyle = col; g.fillRect(0, 0, W, H); noiseOver(g, W, H, 0.09, 3500);
    for (let y = 0; y < H; y += 4) { g.fillStyle = 'rgba(0,0,0,.05)'; g.fillRect(0, y, W, 1); }
    const n = 4, sp = W / n, R0 = 15; for (let r = 0; r < n; r++) for (let k = 0; k <= n; k++) { const x = k * sp + (r % 2 ? sp / 2 : 0), y = r * sp + sp / 2;
      g.fillStyle = 'rgba(0,0,0,.35)'; g.beginPath(); g.arc(x + 2, y + 3, R0 + 1, 0, 7); g.fill(); const gr = g.createRadialGradient(x - 4, y - 5, 1, x, y, R0); gr.addColorStop(0, '#fff6c8'); gr.addColorStop(0.35, col2 || '#d4a845'); gr.addColorStop(1, '#5a4214'); g.fillStyle = gr; g.beginPath(); g.arc(x, y, R0, 0, 7); g.fill();
      const hr = hg.createRadialGradient(x, y, 1, x, y, R0 + 1); hr.addColorStop(0, '#fff'); hr.addColorStop(0.7, '#bbb'); hr.addColorStop(1, '#000'); hg.fillStyle = hr; hg.beginPath(); hg.arc(x, y, R0 + 1, 0, 7); hg.fill(); }
  } else if (kind === 'quilt') { // 胖襖: the padded jacket, quilted in diamonds
    tile = [0.14, 0.14]; rough = 0.9; str = 4; g.fillStyle = col; g.fillRect(0, 0, W, H); noiseOver(g, W, H, 0.08, 3000);
    hg.fillStyle = '#bbb'; hg.fillRect(0, 0, W, H); g.strokeStyle = 'rgba(0,0,0,.28)'; g.lineWidth = 2; hg.strokeStyle = '#222'; hg.lineWidth = 5;
    for (let k = -2; k <= 2; k++) { for (const gg of [g, hg]) { gg.beginPath(); gg.moveTo(k * W / 2, 0); gg.lineTo(k * W / 2 + W, H); gg.moveTo(k * W / 2 + W, 0); gg.lineTo(k * W / 2, H); gg.stroke(); } }
  } else if (kind === 'cloth') { tile = [0.1, 0.1]; rough = 0.92; str = 1.2; g.fillStyle = col; g.fillRect(0, 0, W, H); noiseOver(g, W, H, 0.1, 5000); for (let y = 0; y < H; y += 3) { g.fillStyle = 'rgba(0,0,0,.05)'; g.fillRect(0, y, W, 1); hg.fillStyle = '#444'; hg.fillRect(0, y, W, 1); }
  } else if (kind === 'leather') { tile = [0.12, 0.12]; rough = 0.7; str = 2; g.fillStyle = col; g.fillRect(0, 0, W, H); noiseOver(g, W, H, 0.16, 4000); hg.fillStyle = '#888'; hg.fillRect(0, 0, W, H); noiseOver(hg, W, H, 0.3, 3000);
  } else if (kind === 'fur') { tile = [0.08, 0.08]; rough = 1; str = 3; g.fillStyle = col; g.fillRect(0, 0, W, H); for (let i = 0; i < 2600; i++) { const x = rnd() * W, y = rnd() * H, l = 6 + rnd() * 10; g.strokeStyle = `rgba(${rnd() < 0.5 ? '0,0,0' : '255,240,220'},${0.12 + rnd() * 0.12})`; g.beginPath(); g.moveTo(x, y); g.lineTo(x + rnd() * 3 - 1.5, y + l); g.stroke(); hg.strokeStyle = `rgba(255,255,255,${rnd() * 0.4})`; hg.beginPath(); hg.moveTo(x, y); hg.lineTo(x, y + l); hg.stroke(); }
  } else if (kind === 'trim') { tile = [0.08, 0.04]; rough = 0.6; metal = col2 ? 0.6 : 0; str = 2; g.fillStyle = col; g.fillRect(0, 0, W, H); noiseOver(g, W, H, 0.06); if (col2) { g.fillStyle = col2; g.fillRect(0, H * 0.42, W, H * 0.16); hg.fillStyle = '#fff'; hg.fillRect(0, H * 0.42, W, H * 0.16); }
  } else if (kind === 'skin') { tile = [0.2, 0.2]; rough = 0.62; str = 0.6; g.fillStyle = col; g.fillRect(0, 0, W, H); noiseOver(g, W, H, 0.035, 2500); }
  const map = new THREE.CanvasTexture(c), nm = new THREE.CanvasTexture(heightToNormal(hc, str));
  for (const t of [map, nm]) { t.wrapS = t.wrapT = THREE.RepeatWrapping; t.repeat.set(1 / tile[0], 1 / tile[1]); t.anisotropy = 4; }
  map.encoding = THREE.sRGBEncoding;
  return (TEX[key] = { map, normalMap: nm, rough, metal, tile });
}
function shade(hex, k) { const c = new THREE.Color(hex); if (k > 0) c.lerp(new THREE.Color('#fff'), k); else c.multiplyScalar(1 + k); return '#' + c.getHexString(); }
const MATS = {};
function mat(kind, col, col2, opts) { // a skinned standard material for a pattern (r128: skinned materials need skinning: true)
  const key = [kind, col, col2, opts && opts.rigid ? 'R' : 'S'].join('|'); if (MATS[key]) return MATS[key];
  const P = pattern(kind, col, col2); const m = new THREE.MeshStandardMaterial({ map: P.map, normalMap: P.normalMap, normalScale: new THREE.Vector2(0.9, 0.9), roughness: P.rough, metalness: P.metal, side: THREE.DoubleSide, skinning: !(opts && opts.rigid) });
  return (MATS[key] = m);
}

// ---------------------------------------------------------------------------------------------------------------------
// the body: what the mannequin is made of, read once in its bind pose
// ---------------------------------------------------------------------------------------------------------------------
// every bone belongs to a region of the body; a triangle belongs to the region of the bone that moves most of it
function regionOf(name) {
  if (name === 'Head' || name === 'neck_01') return 'head';
  if (/^(spine_02|spine_03|clavicle_)/.test(name)) return 'chest';
  if (name === 'spine_01') return 'belly';
  if (name === 'pelvis' || name === 'root') return 'hips';
  const m = /^(upperarm|lowerarm|hand|thigh|calf|foot|ball)_(l|r)$/.exec(name);
  if (m) return { upperarm: 'uarm', lowerarm: 'farm', hand: 'hand', thigh: 'thigh', calf: 'calf', foot: 'foot', ball: 'foot' }[m[1]] + m[2].toUpperCase();
  const f = /_(l|r)$/.exec(name); if (f) return 'hand' + f[1].toUpperCase();
  return 'chest';
}
// the axis a region's pattern wraps around (bone to bone in the bind pose); torso regions wrap round the vertical
const AXES = { uarmL: ['upperarm_l', 'lowerarm_l'], uarmR: ['upperarm_r', 'lowerarm_r'], farmL: ['lowerarm_l', 'hand_l'], farmR: ['lowerarm_r', 'hand_r'], handL: ['hand_l', 'middle_01_l'], handR: ['hand_r', 'middle_01_r'],
  thighL: ['thigh_l', 'calf_l'], thighR: ['thigh_r', 'calf_r'], calfL: ['calf_l', 'foot_l'], calfR: ['calf_r', 'foot_r'], footL: ['foot_l', 'ball_l'], footR: ['foot_r', 'ball_r'], head: ['neck_01', 'Head'] };
let BODY = null;
function analyse(gltf) {
  const meshes = []; gltf.scene.traverse(o => { if (o.isSkinnedMesh) meshes.push(o); });
  const skel = meshes[0].skeleton, bones = skel.bones, bi = {}; bones.forEach((b, i) => { bi[b.name] = i; });
  const bindWorld = skel.boneInverses.map(m => new M4().copy(m).invert()), bpos = (n) => new V3().setFromMatrixPosition(bindWorld[bi[n]]);
  const parts = meshes.map((mesh) => {
    const g = mesh.geometry, P = g.attributes.position, N = g.attributes.normal, SI = g.attributes.skinIndex, SW = g.attributes.skinWeight, I = g.index.array, n = P.count;
    // weld by position: glTF splits vertices along hard edges, and an offset by split normals would crack the shell open there
    const key = new Map(), weld = new Int32Array(n), wn = []; for (let i = 0; i < n; i++) { const k = Math.round(P.getX(i) * 4000) + ',' + Math.round(P.getY(i) * 4000) + ',' + Math.round(P.getZ(i) * 4000); if (!key.has(k)) { key.set(k, i); wn[i] = new V3(); } weld[i] = key.get(k); wn[weld[i]].add(new V3(N.getX(i), N.getY(i), N.getZ(i))); }
    const nrm = new Float32Array(n * 3); for (let i = 0; i < n; i++) { const v = wn[weld[i]].clone().normalize(); nrm[i * 3] = v.x; nrm[i * 3 + 1] = v.y; nrm[i * 3 + 2] = v.z; }
    const vreg = []; for (let i = 0; i < n; i++) { let b = 0, bw = -1; for (let k = 0; k < 4; k++) { const w = comp(SW, i, k); if (w > bw) { bw = w; b = comp(SI, i, k); } } vreg[i] = regionOf(bones[b].name); }
    const treg = []; for (let t = 0; t < I.length; t += 3) { const r = [vreg[I[t]], vreg[I[t + 1]], vreg[I[t + 2]]]; treg.push(r[1] === r[2] ? r[1] : r[0]); }
    // the mannequin is built of closed segments (upper arm, thigh, ...): a segment goes wholly to the region that owns most of
    // it, so a sleeve or a tasset is one closed piece with no ragged seam where the weights shade into the next bone
    { const par = new Int32Array(n).map((_, i) => i), f = (x) => { while (par[x] !== x) { par[x] = par[par[x]]; x = par[x]; } return x; };
      for (let t = 0; t < I.length; t += 3) { const a = f(weld[I[t]]), b = f(weld[I[t + 1]]), c = f(weld[I[t + 2]]); par[b] = a; par[c] = a; }
      const votes = new Map(); for (let t = 0, k = 0; t < I.length; t += 3, k++) { const r = f(weld[I[t]]); if (!votes.has(r)) votes.set(r, {}); const v = votes.get(r); v[treg[k]] = (v[treg[k]] || 0) + 1; }
      const own = new Map(); for (const [r, v] of votes) { const tot = Object.values(v).reduce((a, b) => a + b, 0); const best = Object.entries(v).sort((a, b) => b[1] - a[1])[0]; own.set(r, best[1] / tot > 0.6 ? best[0] : null); }
      for (let t = 0, k = 0; t < I.length; t += 3, k++) { const o = own.get(f(weld[I[t]])); if (o) treg[k] = o; else if (treg[k] === 'head' || treg[k] === 'chest') { const cy = (P.getY(I[t]) + P.getY(I[t + 1]) + P.getY(I[t + 2])) / 3, cz = (P.getZ(I[t]) + P.getZ(I[t + 1]) + P.getZ(I[t + 2])) / 3; treg[k] = cy > 1.525 + (cz < 0 ? 0.03 : 0) ? 'head' : 'chest'; } } }
    return { mesh, name: mesh.material.name, P, N, SI, SW, I, n, weld, nrm, vreg, treg };
  });
  // the head, measured in the head bone's own space: what a helmet and a face are sized from
  const head = new THREE.Box3(), hinv = new M4().copy(skel.boneInverses[bi.Head]); const tmp = new V3();
  for (const p of parts) for (let i = 0; i < p.n; i++) if (p.vreg[i] === 'head' && p.P.getY(i) > 1.6) head.expandByPoint(tmp.set(p.P.getX(i), p.P.getY(i), p.P.getZ(i)).applyMatrix4(hinv));
  const headModel = new THREE.Box3(); for (const p of parts) for (let i = 0; i < p.n; i++) if (p.vreg[i] === 'head') headModel.expandByPoint(tmp.set(p.P.getX(i), p.P.getY(i), p.P.getZ(i)));
  BODY = { gltf, parts, bones: bones.map(b => b.name), bi, bindWorld, bpos, head, headModel, clips: {}, restQ: Object.fromEntries(bones.map(b => [b.name, b.quaternion.clone()])) };
  for (const c of gltf.animations) BODY.clips[c.name] = c;
  return BODY;
}

// ---------------------------------------------------------------------------------------------------------------------
// blocks: the man is made of rigid boxes, one or more to a bone, each moved wholly by its bone (weight 1): nothing bends, so
// nothing can stretch or crease, and the 65-bone rig keeps every joint of the animations (fingers too). Armor is the same
// boxes grown outward by the armor's thickness: a covered body box lies strictly inside its armor box on the same bone, in
// every pose, so the body can never show through. Layers are thicknesses (shirt < coat < plates). An ink line round every
// visible box (an inverted hull) gives the woodblock look.
// box = { bi, c, ax: [side, long, depth], h: [half sizes], flare (added to the side and depth half sizes at the +long end), vdir }
// ---------------------------------------------------------------------------------------------------------------------
const X = new V3(1, 0, 0), Y = new V3(0, 1, 0), Z = new V3(0, 0, 1);
const FL = (f) => Array.isArray(f) ? f : [f || 0, f || 0];
function mkBox(bone, c, ax, h, o) { const b = Object.assign({ bone, bi: BODY.bi[bone], c, ax, h, ch: 0, vdir: ax[1].y > 0.5 ? 1 : -1 }, o || {}); b.flare = FL(b.flare); b.flareN = FL(b.flareN); return b; }
function aabb(bone, mn, mx, o) { return mkBox(bone, new V3((mn[0] + mx[0]) / 2, (mn[1] + mx[1]) / 2, (mn[2] + mx[2]) / 2), [X, Y, Z], [(mx[0] - mn[0]) / 2, (mx[1] - mn[1]) / 2, (mx[2] - mn[2]) / 2], o); }
function seg(bone, A, B, w, d, e0, e1, o) { // a box along a bone, A to B, overrunning the joints by e0 and e1 so a bent joint shows no gap
  const a1 = B.clone().sub(A), L = a1.length(); a1.normalize(); let ref = (o && o.ref) || Z; if (Math.abs(ref.dot(a1)) > 0.9) ref = Y;
  const a2 = ref.clone().sub(a1.clone().multiplyScalar(ref.dot(a1))).normalize(), a0 = new V3().crossVectors(a1, a2);
  const c = A.clone().add(a1.clone().multiplyScalar((L + e1 - e0) / 2)); if (o && o.off) c.add(o.off); return mkBox(bone, c, [a0, a1, a2], [w / 2, (L + e0 + e1) / 2, d / 2], o); }
function joint(bone, P, r) { return mkBox(bone, P.clone(), [X, Y, Z], [r, r, r], { ch: r * 0.55, bev: r * 0.45 }); }
function grow(b, t, o) { const f = FL(o && o.flare); return Object.assign({}, b, { h: [b.h[0] + t, b.h[1] + t, b.h[2] + t], flare: [b.flare[0] + f[0], b.flare[1] + f[1]], ch: b.ch ? b.ch + t * 0.4 : 0 }); } /* the chamfer grows less than the box: every face of the armor stands outside the body's */
function rel(b, along, h, o) { // a box on the same bone, placed along another box's long axis (along: -1 its near end .. +1 its far end)
  const c = b.c.clone().addScaledVector(b.ax[1], along * b.h[1]); if (o && o.out) c.addScaledVector(b.ax[2], o.out); return Object.assign({}, b, { c, h, flare: FL(o && o.flare), flareN: [0, 0], ch: o && o.ch !== undefined ? o.ch : b.ch }); }
// a block is a prism round its long axis: an octagon when chamfered (a square otherwise), its section scaled from the near
// end's flare to the far end's; with a bevel (bev, metres) the ends are cut in too, so it reads as a cut stone, not a cube
function ring(b, t, inset, inf) { const k = (t + 1) / 2, f0 = lerp(b.flareN[0], b.flare[0], k), f2 = lerp(b.flareN[1], b.flare[1], k);
  const a = b.h[0] + inf + f0 - inset, d = b.h[2] + inf + f2 - inset, c = Math.max(0.0005, Math.min(b.ch + inset * 0.4, a * 0.8, d * 0.8)); /* every ring the same number of sides */
  const pts = b.ch > 0.002 || b.bev ? [[a, -d + c], [a, d - c], [a - c, d], [-a + c, d], [-a, d - c], [-a, -d + c], [-a + c, -d], [a - c, -d]] : [[a, -d], [a, d], [-a, d], [-a, -d]];
  const y = t * (b.h[1] + inf); return pts.map(([x, z]) => b.c.clone().addScaledVector(b.ax[0], x).addScaledVector(b.ax[1], y).addScaledVector(b.ax[2], z)); }
function acc() { return { pos: [], nor: [], uv: [], si: [], sw: [], idx: [] }; }
function emit(A, b, inf) { inf = inf || 0; const q = new V3(), e = b.bev ? Math.min(0.8, b.bev / (b.h[1] + inf)) : 0, eN = b.bevN !== undefined ? Math.min(0.8, b.bevN / (b.h[1] + inf)) : e;
  const R = e || eN ? [ring(b, -1, eN ? b.bevN !== undefined ? b.bevN : b.bev : 0, inf), ring(b, -1 + eN, 0, inf), ring(b, 1 - e, 0, inf), ring(b, 1, e ? b.bev : 0, inf)] : [ring(b, -1, 0, inf), ring(b, 1, 0, inf)], n = R[0].length;
  const vert = (p, nn, u, v) => { A.pos.push(p.x, p.y, p.z); A.nor.push(nn.x, nn.y, nn.z); A.uv.push(u, v); A.si.push(b.bi, 0, 0, 0); A.sw.push(1, 0, 0, 0); return A.pos.length / 3 - 1; };
  const along = (p) => q.subVectors(p, b.c).dot(b.ax[1]) * b.vdir; /* patterns run down the long axis, in metres, so a plate is a plate's size on any block */
  for (let r = 0; r + 1 < R.length; r++) { const lo = R[r], hi = R[r + 1]; let u = 0;
    for (let i = 0; i < n; i++) { const k = (i + 1) % n, P = [lo[i], hi[i], hi[k], lo[k]]; const nn = new V3().subVectors(P[1], P[0]).add(new V3().subVectors(P[2], P[3])).cross(new V3().subVectors(P[3], P[0])).normalize(); const w = lo[i].distanceTo(lo[k]);
      if (nn.lengthSq() < 0.5) continue; const v0 = vert(P[0], nn, u, along(P[0])), v1 = vert(P[1], nn, u, along(P[1])), v2 = vert(P[2], nn, u + w, along(P[2])), v3 = vert(P[3], nn, u + w, along(P[3])); A.idx.push(v0, v1, v2, v0, v2, v3); u += w; } }
  for (const [Rg, s] of [[R[R.length - 1], 1], [R[0], -1]]) { const nn = b.ax[1].clone().multiplyScalar(s);
    const base = A.pos.length / 3; for (const p of Rg) { q.subVectors(p, b.c); vert(p, nn, q.dot(b.ax[0]) + 0.5, q.dot(b.ax[2]) + 0.5); }
    for (let i = 1; i < n - 1; i++) if (s > 0) A.idx.push(base, base + i + 1, base + i); else A.idx.push(base, base + i, base + i + 1); } }
function toGeo(A) { const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(A.pos, 3)); g.setAttribute('normal', new THREE.Float32BufferAttribute(A.nor, 3)); g.setAttribute('uv', new THREE.Float32BufferAttribute(A.uv, 2));
  g.setAttribute('skinIndex', new THREE.Uint16BufferAttribute(A.si, 4)); g.setAttribute('skinWeight', new THREE.Float32BufferAttribute(A.sw, 4)); g.setIndex(A.idx); g.computeBoundingSphere(); return g; }

// the body in blocks, by region (the regions the armor sets name). Not the mannequin's build: a drawn one, on the same joints.
// A big squared head with a jaw, nose and ears; a deep chest wide at the shoulder over a narrow waist; arms heavy at the
// shoulder and forearm, tapering to the joint below; big fists and boots. Every block is chamfered along its length.
function bodyBoxes() {
  if (BODY.boxes) return BODY.boxes; const P = BODY.bpos, R = {}; const add = (r, b) => (R[r] = R[r] || []).push(b);
  add('hips', aabb('pelvis', [-0.15, 0.83, -0.115], [0.15, 1.0, 0.1], { hem: -1, ch: 0.035, flareN: [0.01, 0.005], bev: 0.02 }));
  add('belly', aabb('spine_01', [-0.12, 1.0, -0.1], [0.12, 1.165, 0.1], { ch: 0.035, flare: [0.035, 0.01] }));
  add('chest', aabb('spine_02', [-0.15, 1.165, -0.112], [0.15, 1.31, 0.12], { ch: 0.04, flare: [0.03, 0.012] }));
  add('chest', aabb('spine_03', [-0.185, 1.31, -0.125], [0.185, 1.465, 0.13], { ch: 0.045, flare: [-0.04, -0.04], bev: 0.03 }));
  add('neck', aabb('neck_01', [-0.058, 1.43, -0.07], [0.058, 1.575, 0.045], { ch: 0.018, flareN: [0.03, 0.01] }));
  add('head', aabb('Head', [-0.118, 1.545, -0.125], [0.118, 1.83, 0.122], { ch: 0.042, bev: 0.035, bevN: 0.05, flareN: [-0.022, -0.012] })); /* one cut block: brow and crown bevelled, the jaw drawn in to the chin */
  for (const s of ['l', 'r']) { const S = s.toUpperCase(), b = (n) => P(n + '_' + s);
    const ua = seg('upperarm_' + s, b('upperarm'), b('lowerarm'), 0.112, 0.115, 0.0, 0.03, { hem: 1, ch: 0.03, flare: [-0.022, -0.025], bev: 0.03, bevN: 0 }); add('uarm' + S, ua);
    { const J = joint('upperarm_' + s, b('upperarm').add(new V3(0, -0.005, 0.0)), 0.082); J.h = [0.084, 0.08, 0.082]; add('uarm' + S, J); } /* the shoulder: a cut cap round the joint itself, over the chest's corner, so the arm turns out of the trunk through it */
    add('farm' + S, seg('lowerarm_' + s, b('lowerarm'), b('hand'), 0.112, 0.106, 0.035, 0.0, { hem: 1, ch: 0.028, flare: [-0.035, -0.03], bevN: 0.03, bev: 0 }));
    add('farm' + S, joint('lowerarm_' + s, b('lowerarm'), 0.05)); /* the elbow: a cut knuckle on the forearm's bone, so a bent arm turns a corner instead of showing the end of a block */
    add('hand' + S, seg('hand_' + s, b('hand'), b('middle_01'), 0.052, 0.108, 0.008, 0.006, { off: new V3(0, 0, -0.006), ch: 0.012, bev: 0.01 }));
    for (const f of ['index', 'middle', 'ring', 'pinky']) for (let k = 1; k <= 3; k++) add('hand' + S, seg(f + '_0' + k + '_' + s, b(f + '_0' + k), k < 3 ? b(f + '_0' + (k + 1)) : b(f + '_04_leaf'), 0.03, 0.025, 0.006, 0.003, { ch: 0.006 }));
    for (let k = 1; k <= 3; k++) add('hand' + S, seg('thumb_0' + k + '_' + s, b('thumb_0' + k), k < 3 ? b('thumb_0' + (k + 1)) : b('thumb_04_leaf'), 0.032, 0.032, 0.008, 0.003, { ch: 0.007 }));
    add('thigh' + S, seg('thigh_' + s, b('thigh'), b('calf'), 0.17, 0.18, 0.05, 0.035, { hem: 1, ch: 0.04, flare: [-0.04, -0.035], bev: 0.035, bevN: 0 }));
    add('calf' + S, seg('calf_' + s, b('calf'), b('foot'), 0.14, 0.15, 0.03, 0.0, { hem: -1, ch: 0.035, flare: [-0.055, -0.06], bevN: 0.035, bev: 0 }));
    add('calf' + S, joint('calf_' + s, b('calf'), 0.062)); /* the knee */
    const x = b('foot').x; add('foot' + S, aabb('foot_' + s, [x - 0.062, 0, -0.11], [x + 0.062, 0.15, 0.12], { ch: 0.02, flare: [-0.006, -0.02], bev: 0.015, bevN: 0 })); add('foot' + S, aabb('ball_' + s, [x - 0.06, 0, 0.12], [x + 0.06, 0.072, 0.218], { ch: 0.018, flare: [-0.004, -0.02], bev: 0.02, bevN: 0 })); }
  return (BODY.boxes = R);
}
// solid (unpatterned) skinned materials, and a key for every material a set uses
const SOLID = {};
function solid(col, rough, metal) { const k = col + '|' + rough + '|' + (metal || 0); return SOLID[k] || (SOLID[k] = new THREE.MeshStandardMaterial({ color: new THREE.Color(col).convertSRGBToLinear(), roughness: rough, metalness: metal || 0, skinning: true })); }
const STEEL = ['s', '#3c3f44', 0.4, 0.8], GILT = ['s', '#c09440', 0.35, 0.85], HAIRM = ['s', '#17120e', 0.8], REDM = ['s', '#a8231a', 0.95];
function matOf(k) { return k[0] === 's' ? solid(k[1], k[2], k[3]) : mat(k[1], k[2], k[3]); }
const LINE = new THREE.MeshBasicMaterial({ color: 0x15100b, side: THREE.BackSide, skinning: true });
const INK = 0.0065;
// helmets, in blocks on the head bone, round the head box with a margin: a bowl over the crown, a cap stepped in above it
function helmetBoxes(kind, hairOnly) {
  const H = bodyBoxes().head[0], out = [], c = H.c, h = H.h, top = c.y + h[1], brow = top - 0.065, put = (m, mn, mx, o) => out.push([m, aabb('Head', mn, mx, Object.assign({ ch: 0.028, bev: 0.008 }, o))]);
  const bx = h[0] + 0.014, bz = h[2] + 0.014, z0 = c.z;
  const bowl = (m, rise, capH, capIn) => { put(m, [-bx, brow, z0 - bz], [bx, top + rise, z0 + bz]); put(m, [-bx + 0.012, top + rise, z0 - bz + 0.012], [bx - 0.012, top + rise + capH, z0 + bz - 0.012], { flare: -capIn }); return top + rise + capH; };
  const spike = (m, y, len, w) => put(m, [-w, y, z0 - w], [w, y + len, z0 + w], { flare: -w * 0.6 });
  const tassel = (y) => put(REDM, [-0.035, y - 0.07, z0 - 0.035], [0.035, y, z0 + 0.035], { flare: -0.026 });
  const flaps = (m, len, spread) => { put(m, [-bx - 0.004, brow - len, z0 - bz - 0.018], [bx + 0.004, brow + 0.01, z0 - bz + 0.006], { flare: 0, }); for (const s of [-1, 1]) put(m, s < 0 ? [-bx - 0.02, brow - len * 0.85, z0 - bz] : [bx, brow - len * 0.85, z0 - bz], s < 0 ? [-bx, brow + 0.01, z0 + bz * 0.25] : [bx + 0.02, brow + 0.01, z0 + bz * 0.25]); };
  if (hairOnly) { put(HAIRM, [-h[0] - 0.006, top - 0.07, z0 - h[2] - 0.006], [h[0] + 0.006, top + 0.012, z0 + h[2] - 0.03]); return out; }
  if (kind === 'ming' || kind === 'mingHigh') { const t = bowl(STEEL, 0.02, 0.04, 0.05); put(GILT, [-bx - 0.004, brow, z0 - bz - 0.004], [bx + 0.004, brow + 0.022, z0 + bz + 0.004]);
    const sp = kind === 'mingHigh' ? 0.2 : 0.12; spike(GILT, t, sp, 0.008); tassel(t + sp * 0.55); flaps(kind === 'mingHigh' ? ['p', 'lamellar', '#232427', '#8c1e18'] : ['p', 'studs', '#a8261d', '#d6aa48'], 0.12, 0); }
  else if (kind === 'qing') { const t = bowl(['s', '#2a2620', 0.45, 0.7], 0.035, 0.05, 0.055); put(GILT, [-bx - 0.018, brow, z0 - bz - 0.018], [bx + 0.018, brow + 0.012, z0 + bz + 0.045]); /* the visor rim, out over the brow */
    spike(GILT, t, 0.26, 0.006); put(GILT, [-0.016, t, z0 - 0.016], [0.016, t + 0.03, z0 + 0.016]); tassel(t + 0.2); flaps(['p', 'studs', '#2a2a30', '#c9a24a'], 0.16, 0); }
  else if (kind === 'rattan') { const R = ['p', 'quilt', '#b08848']; put(R, [-bx - 0.03, brow - 0.005, z0 - bz - 0.03], [bx + 0.03, brow + 0.012, z0 + bz + 0.03]); put(R, [-bx, brow + 0.012, z0 - bz], [bx, top + 0.03, z0 + bz], { flare: -0.04 }); }
  else if (kind === 'felt') { const F = ['s', '#2a2724', 1]; put(F, [-bx, brow + 0.01, z0 - bz], [bx, top + 0.02, z0 + bz], { flare: -0.03 }); put(F, [-bx - 0.022, brow + 0.004, z0 - bz - 0.022], [bx + 0.022, brow + 0.035, z0 + bz + 0.022], { flare: 0.006 }); tassel(top + 0.07); }
  else if (kind === 'fur') { const F = ['p', 'fur', '#7a5a36']; put(F, [-bx - 0.03, brow - 0.01, z0 - bz - 0.03], [bx + 0.03, brow + 0.05, z0 + bz + 0.03]); put(['s', '#7a2a1c', 0.9], [-bx + 0.005, brow + 0.05, z0 - bz + 0.005], [bx - 0.005, top + 0.05, z0 + bz - 0.005], { flare: -0.04 }); }
  return out;
}
function queueBoxes() { const H = bodyBoxes().head[0], out = []; let y = H.c.y + 0.02, z = H.c.z - H.h[2] - 0.012; /* 辮: the Manchu queue, braided blocks down the back */
  for (let i = 0; i < 6; i++) { const w = 0.016 - i * 0.0014; out.push([HAIRM, aabb('Head', [-w, y - 0.04, z - w], [w, y, z + w])]); y -= 0.042; z -= 0.004; } return out; }
// a set's geometry, shared by every man who wears it: the visible body, the covered body (only for the clipping check), one
// mesh per material, and the ink line round all that shows
const SETGEO = {};
function setGeo(setKey) {
  if (SETGEO[setKey]) return SETGEO[setKey]; const S = ARMOR[setKey], BB = bodyBoxes(), covered = new Set(); S.pieces.forEach(P => P.regions.forEach(r => covered.add(r)));
  const skin = acc(), hid = acc(), line = acc(), G = new Map(), g = (k) => { const key = k.join('|'); if (!G.has(key)) G.set(key, { k, A: acc() }); return G.get(key).A; };
  const show = (k, b) => { emit(k ? g(k) : skin, b); emit(line, b, INK); };
  for (const r in BB) for (const b of BB[r]) { if (covered.has(r)) emit(hid, b); else show(null, b); }
  let torsoT = 0.02;
  for (const P of S.pieces) { const T = typeof P.t === 'object' ? P.t : { t0: P.t, flare: 0 }, K = ['p', P.kind, P.col, P.col2], RK = P.rim ? ['p', P.rim[0], P.rim[1], P.rim[2]] : null; if (P.regions.includes('chest')) torsoT = T.t0;
    for (const r of P.regions) for (const b of BB[r]) { const a = grow(b, T.t0, { flare: T.flare }); show(K, a);
      const NEXT = { uarm: 'farm', farm: 'hand', thigh: 'calf', calf: 'thigh', hips: 'thigh' }, rr = /^(uarm|farm|thigh|calf|hips)(L|R)?$/.exec(r), nx = rr && NEXT[rr[1]], cont = nx && (rr[1] === 'hips' ? P.regions.includes('thighL') : P.regions.includes(nx + rr[2]));
      if (RK && b.hem && !cont && !b.joint) { const f = b.hem > 0 ? a.flare : a.flareN; show(RK, rel(a, b.hem, [a.h[0] + f[0] + 0.006, 0.02, a.h[2] + f[1] + 0.006], { flare: 0 })); /* the hem or cuff: a border band round the end of the piece */ }
      if (T.pauldron && /^uarm/.test(r) && b === BB[r][0]) { const cap = rel(a, -1, [a.h[0] + 0.022, 0.085, a.h[2] + 0.022], { flare: 0.02 }); cap.c = cap.c.clone().addScaledVector(a.ax[1], 0.075); show(K, cap); if (RK) show(RK, rel(cap, 1, [cap.h[0] + 0.02 + 0.006, 0.016, cap.h[2] + 0.02 + 0.006], { ch: cap.ch })); } /* 披膊: a shoulder guard over the top of the arm */ } }
  if (S.mirror) { const c3 = BB.chest[1]; show(S.mirror, aabb('spine_03', [-0.065, 1.33, c3.c.z + c3.h[2] + torsoT], [0.065, 1.44, c3.c.z + c3.h[2] + torsoT + 0.012])); } /* 護心鏡: the round mirror plate over the heart, here squared */
  for (const [k, b] of S.helmet ? helmetBoxes(S.helmet) : helmetBoxes(null, true)) show(k, b);
  if (S.face === 'jin') for (const [k, b] of queueBoxes()) show(k, b);
  return (SETGEO[setKey] = { skin: toGeo(skin), hid: hid.pos.length ? toGeo(hid) : null, line: toGeo(line), parts: [...G.values()].map(e => ({ k: e.k, geo: toGeo(e.A) })), tris: (skin.idx.length + line.idx.length + [...G.values()].reduce((s, e) => s + e.A.idx.length, 0)) / 3 });
}

// ---------------------------------------------------------------------------------------------------------------------
// armor sets: what a man wears, piece by piece. Thickness is the layer: shirt 8 mm < coat 20 mm < plates 30-45 mm, so the
// layers can never pass through one another either. Tassets and shoulder guards flare: thicker the further down the bone.
// Sources: 出警入蹕圖 and 平番得勝圖 for Ming coats, helmets and colours; 《武備志》卷一百零五 甲冑; 《欽定大清會典圖》 and 《滿文老檔》 for the
// banner coats (studded 綿甲, the banner colours, red borders on the bordered banners); 紀效新書 for the southern rattan-shield man.
// ---------------------------------------------------------------------------------------------------------------------
const TORSO = ['chest', 'belly', 'hips'], ARMS = ['uarmL', 'uarmR', 'farmL', 'farmR'], UARM = ['uarmL', 'uarmR'], FARM = ['farmL', 'farmR'], THIGH = ['thighL', 'thighR'], CALF = ['calfL', 'calfR'], FOOT = ['footL', 'footR'], HAND = ['handL', 'handR'];
const flareDown = (t0, k) => ({ t0, flare: k * 0.32 }); /* wider toward the knee: the skirt stands off the leg like a real one */
const flareArm = (t0, k) => ({ t0, flare: k * 0.3, pauldron: true }); /* shoulder guards stand out toward the elbow */
const PIECE = (regions, t, kind, col, col2, rim, extra) => Object.assign({ regions, t, kind, col, col2, rim }, extra || {});
const ARMOR = {
  ming_jacket: { name: '明 · 胖襖', en: 'Ming soldier · padded red jacket', helmet: 'felt', face: 'ming',
    pieces: [PIECE(CALF.concat(FOOT), 0.010, 'leather', '#1d1915', null, ['trim', '#1d1915']), PIECE(THIGH, 0.008, 'cloth', '#2a3446', null, ['trim', '#2a3446']),
      PIECE(TORSO.concat(ARMS), 0.02, 'quilt', '#9e2b20', null, ['trim', '#2b2320'])] },
  ming_studded: { name: '明 · 布面甲', en: 'Ming heavy foot · red studded coat', helmet: 'ming', face: 'ming', mirror: GILT,
    pieces: [PIECE(CALF.concat(FOOT), 0.010, 'leather', '#1d1915', null, ['trim', '#1d1915']), PIECE(FARM, 0.016, 'leather', '#3a2a1c', null, ['trim', '#a8823c', '#e0b850']),
      PIECE(TORSO, 0.024, 'studs', '#a8261d', '#d6aa48', ['trim', '#1c1814', '#d6aa48']), PIECE(THIGH, flareDown(0.03, 0.12), 'studs', '#a8261d', '#d6aa48', ['trim', '#1c1814', '#d6aa48']),
      PIECE(UARM, flareArm(0.032, 0.09), 'studs', '#a8261d', '#d6aa48', ['trim', '#1c1814', '#d6aa48'])] },
  ming_lamellar: { name: '明 · 札甲', en: 'Ming officer · black-lacquered lamellar', helmet: 'mingHigh', face: 'mingBeard', mirror: ['s', '#9aa2a8', 0.25, 0.9],
    pieces: [PIECE(CALF.concat(FOOT), 0.010, 'leather', '#1a1613', null, ['trim', '#1a1613']), PIECE(HAND, 0.004, 'leather', '#2c2016', null, null), PIECE(FARM, 0.02, 'lamellar', '#2a2b2e', '#8c1e18', ['trim', '#8c1e18']),
      PIECE(TORSO, 0.03, 'lamellar', '#232427', '#8c1e18', ['trim', '#8c1e18', '#d8b04a']), PIECE(THIGH, flareDown(0.036, 0.13), 'lamellar', '#232427', '#8c1e18', ['trim', '#8c1e18', '#d8b04a']),
      PIECE(UARM, flareArm(0.04, 0.1), 'lamellar', '#232427', '#8c1e18', ['trim', '#8c1e18', '#d8b04a'])] },
  qi_rattan: { name: '戚家軍 · 藤牌手', en: 'Qi Jiguang\'s southerner · rattan-shield man', helmet: 'rattan', face: 'young',
    pieces: [PIECE(FOOT, 0.006, 'leather', '#6b5634', null, null), PIECE(CALF, 0.012, 'cloth', '#d8cfb6', null, ['trim', '#8a7a5c']), PIECE(THIGH, 0.008, 'cloth', '#3c4650', null, ['trim', '#3c4650']),
      PIECE(TORSO.concat(UARM), 0.016, 'cloth', '#4a5a6a', null, ['trim', '#c8b48a'])] },
  jin_yellow: { name: '後金 · 正黃旗', en: 'Jin bannerman · Plain Yellow', helmet: 'qing', face: 'jin', banner: '#d9a62a',
    pieces: [PIECE(CALF.concat(FOOT), 0.010, 'leather', '#1a1613', null, ['trim', '#1a1613']), PIECE(FARM, 0.016, 'cloth', '#1f2a3a', null, ['trim', '#d9a62a']),
      PIECE(TORSO, 0.024, 'studs', '#d9a62a', '#c79a3a', ['trim', '#2a1e14', '#c79a3a']), PIECE(THIGH, flareDown(0.03, 0.12), 'studs', '#d9a62a', '#c79a3a', ['trim', '#2a1e14', '#c79a3a']),
      PIECE(UARM, flareArm(0.032, 0.09), 'studs', '#d9a62a', '#c79a3a', ['trim', '#2a1e14', '#c79a3a'])] },
  jin_white: { name: '後金 · 正白旗', en: 'Jin bannerman · Plain White (the Jin campaign\'s niru)', helmet: 'qing', face: 'jin', banner: '#ece6d6',
    pieces: [PIECE(CALF.concat(FOOT), 0.010, 'leather', '#1a1613', null, ['trim', '#1a1613']), PIECE(FARM, 0.016, 'cloth', '#1f2a3a', null, ['trim', '#ece6d6']),
      PIECE(TORSO, 0.024, 'studs', '#ece6d6', '#b8923a', ['trim', '#22252c', '#b8923a']), PIECE(THIGH, flareDown(0.03, 0.12), 'studs', '#ece6d6', '#b8923a', ['trim', '#22252c', '#b8923a']),
      PIECE(UARM, flareArm(0.032, 0.09), 'studs', '#ece6d6', '#b8923a', ['trim', '#22252c', '#b8923a'])] },
  jin_blue_b: { name: '後金 · 鑲藍旗', en: 'Jin bannerman · Bordered Blue (red border)', helmet: 'qing', face: 'jin', banner: '#2c4a8a',
    pieces: [PIECE(CALF.concat(FOOT), 0.010, 'leather', '#1a1613', null, ['trim', '#1a1613']), PIECE(FARM, 0.016, 'cloth', '#1f2a3a', null, ['trim', '#b32a20']),
      PIECE(TORSO, 0.024, 'studs', '#2c4a8a', '#c9a24a', ['trim', '#b32a20', '#c9a24a']), PIECE(THIGH, flareDown(0.03, 0.12), 'studs', '#2c4a8a', '#c9a24a', ['trim', '#b32a20', '#c9a24a']),
      PIECE(UARM, flareArm(0.032, 0.09), 'studs', '#2c4a8a', '#c9a24a', ['trim', '#b32a20', '#c9a24a'])] },
  mongol: { name: '蒙古 · 皮甲', en: 'Khorchin Mongol · leather lamellar and fur', helmet: 'fur', face: 'mongol',
    pieces: [PIECE(CALF.concat(FOOT), 0.012, 'leather', '#3a2414', null, ['trim', '#3a2414']), PIECE(THIGH, 0.01, 'cloth', '#5a3a24', null, ['trim', '#5a3a24']),
      PIECE(ARMS, 0.018, 'cloth', '#6a4a2a', null, ['fur', '#8a6a44']), PIECE(TORSO, 0.028, 'lamellar', '#6a4528', '#2a1a10', ['fur', '#8a6a44'])] },
  bare: { name: '素 · 無甲', en: 'the mannequin, nothing on', helmet: null, face: 'ming', pieces: [] },
};
const SKIN = { ming: '#c8946a', mingBeard: '#bf8a60', young: '#cf9c70', jin: '#c08a5e', mongol: '#b07a4e' };

// ---------------------------------------------------------------------------------------------------------------------
// the face: painted on the front of the head block, rigid on the head bone
// ---------------------------------------------------------------------------------------------------------------------
// the face: a patch laid on the real head surface (each point cast onto the head and lifted 2.5 mm), with eyes, brows and a mouth
// drawn for a few looks and expressions (calm, the shout of a blow, pain)
function faceTex(kind, expr) {
  const key = 'face:' + kind + ':' + expr; if (TEX[key]) return TEX[key]; const W = 256, H = 256, c = document.createElement('canvas'); c.width = W; c.height = H; const g = c.getContext('2d');
  const ink = '#1a120c', eyeY = 108, ex = 44, mouthY = 182;
  // brows: drawn down and in for the shout, up in the middle for pain
  g.strokeStyle = ink; g.lineCap = 'round'; g.lineWidth = kind === 'young' ? 6 : 8;
  for (const s of [-1, 1]) { g.beginPath(); const inY = expr === 'shout' ? eyeY - 10 : expr === 'pain' ? eyeY - 30 : eyeY - 22, outY = expr === 'pain' ? eyeY - 16 : eyeY - 24; g.moveTo(W / 2 + s * 14, inY); g.quadraticCurveTo(W / 2 + s * 34, eyeY - 30, W / 2 + s * 62, outY); g.stroke(); }
  for (const s of [-1, 1]) { const cx = W / 2 + s * ex; // eyes: an almond with the heavy upper lid
    g.fillStyle = '#efe6d8'; g.beginPath(); g.ellipse(cx, eyeY, 17, expr === 'pain' ? 4 : expr === 'shout' ? 8 : 6.5, 0, 0, 7); g.fill();
    if (expr !== 'pain') { g.fillStyle = '#2a1a10'; g.beginPath(); g.arc(cx + s * -1.5, eyeY + 0.5, 6, 0, 7); g.fill(); }
    g.strokeStyle = ink; g.lineWidth = 4; g.beginPath(); g.moveTo(cx - 19, eyeY + 1); g.quadraticCurveTo(cx, eyeY - 12, cx + 19, eyeY - 1); g.stroke(); }
  g.strokeStyle = 'rgba(90,50,30,.55)'; g.lineWidth = 4; g.beginPath(); g.moveTo(W / 2 - 4, eyeY + 18); g.quadraticCurveTo(W / 2 - 9, 150, W / 2 - 10, 156); g.lineTo(W / 2 + 8, 158); g.stroke(); /* the nose, a shadow line */
  if (expr === 'shout') { g.fillStyle = '#3a0f0c'; g.beginPath(); g.ellipse(W / 2, mouthY + 4, 20, 14, 0, 0, 7); g.fill(); g.fillStyle = '#e8e0d0'; g.fillRect(W / 2 - 14, mouthY - 8, 28, 5); }
  else { g.strokeStyle = '#5a2a1e'; g.lineWidth = 5; g.beginPath(); g.moveTo(W / 2 - 20, mouthY + (expr === 'pain' ? 4 : 0)); g.quadraticCurveTo(W / 2, mouthY + (expr === 'pain' ? -6 : 3), W / 2 + 20, mouthY + (expr === 'pain' ? 4 : 0)); g.stroke(); }
  if (kind === 'mingBeard' || kind === 'jin' || kind === 'mongol') { g.strokeStyle = ink; g.lineWidth = 6; for (const s of [-1, 1]) { g.beginPath(); g.moveTo(W / 2 + s * 4, mouthY - 14); g.quadraticCurveTo(W / 2 + s * 26, mouthY - 16, W / 2 + s * 36, mouthY + (kind === 'mongol' ? 18 : 6)); g.stroke(); } }
  if (kind === 'mingBeard') { g.fillStyle = 'rgba(26,18,12,.9)'; g.beginPath(); g.moveTo(W / 2 - 18, mouthY + 22); g.quadraticCurveTo(W / 2, mouthY + 70, W / 2 + 18, mouthY + 22); g.fill(); }
  const t = new THREE.CanvasTexture(c); t.encoding = THREE.sRGBEncoding; return (TEX[key] = t);
}
let FACE_GEO = null;
function faceGeo() { if (FACE_GEO) return FACE_GEO; const H = bodyBoxes().head[0], top = H.c.y + H.h[1]; const g = new THREE.PlaneGeometry(0.15, 0.19); g.translate(H.c.x, top - 0.05 - 0.095, H.c.z + H.h[2] + 0.0015); return (FACE_GEO = g); }

// ---------------------------------------------------------------------------------------------------------------------
// weapons: rigid on a hand or forearm. The grip is read off the hand itself in the bind pose (finger direction, the line of
// the knuckles from little finger to index, the palm side where the thumb sits), so the blade comes out of the fist on the
// thumb side with the edge where the knuckles point, whatever the bone axes happen to be.
// ---------------------------------------------------------------------------------------------------------------------
function gripFrame(side) { // model-space matrix of a fist's grip: +Y out of the thumb side, +X where the knuckles point (the edge), origin inside the fist
  const k = 'grip' + side; if (BODY[k]) return BODY[k]; const b = (n) => BODY.bpos(n + '_' + side);
  const H = b('hand'), fd = b('middle_01').sub(H).normalize(), across = b('index_01').sub(b('pinky_01')); across.sub(fd.clone().multiplyScalar(across.dot(fd))).normalize();
  let palm = new V3().crossVectors(fd, across).normalize(); if (b('thumb_01').sub(H).dot(palm) < 0) palm.negate();
  const o = H.clone().add(fd.clone().multiplyScalar(0.075)).add(palm.clone().multiplyScalar(0.028));
  const m = new M4().makeBasis(fd, across, new V3().crossVectors(fd, across)).setPosition(o); return (BODY[k] = { m, fd, across, palm, o });
}
function wpnMat(c, r, mt) { return new THREE.MeshStandardMaterial({ color: new THREE.Color(c).convertSRGBToLinear(), roughness: r, metalness: mt || 0, flatShading: true }); }
const WEAPON = {
  dao: { name: '腰刀 Dao', hand: 'r', build() { // the Ming 腰刀: a curved single-edged blade, a disc guard, a cord-wrapped grip
    const g = new THREE.Group(), s = new THREE.Shape(); const L = 0.74, w = 0.034, curve = 0.05; s.moveTo(0, 0); for (let i = 0; i <= 5; i++) { const t = i / 5; s.lineTo(w * (1 - t * 0.35) + curve * t * t, t * L); } s.lineTo(curve + 0.002, L + 0.02); for (let i = 5; i >= 0; i--) { const t = i / 5; s.lineTo(curve * t * t - 0.004, t * L); }
    const bl = new THREE.Mesh(new THREE.ExtrudeGeometry(s, { depth: 0.006, bevelEnabled: false }), wpnMat(0xd2d8dc, 0.22, 0.95)); bl.position.set(-0.016, 0.045, -0.003); g.add(bl);
    const gd = new THREE.Mesh(new THREE.CylinderGeometry(0.042, 0.042, 0.01, 8), wpnMat(0xb8913a, 0.35, 0.85)); gd.position.y = 0.04; g.add(gd);
    const gr = new THREE.Mesh(new THREE.BoxGeometry(0.03, 0.2, 0.034), wpnMat(0x3a1e14, 0.9)); gr.position.y = -0.055; g.add(gr);
    const pm = new THREE.Mesh(new THREE.BoxGeometry(0.038, 0.03, 0.04), wpnMat(0xb8913a, 0.35, 0.85)); pm.position.y = -0.165; g.add(pm); return g; } },
  spear: { name: '長槍 Spear', hand: 'r', two: true, build() { // the long spear: a wax-wood shaft, a leaf point, a red horsehair tassel under the head
    const g = new THREE.Group(); const sh = new THREE.Mesh(new THREE.BoxGeometry(0.032, 3.2, 0.032), wpnMat(0x8a6a44, 0.75)); sh.position.y = 0.55; g.add(sh);
    const pt = new THREE.Mesh(new THREE.ConeGeometry(0.03, 0.26, 4), wpnMat(0xd0d6da, 0.25, 0.95)); pt.scale.z = 0.35; pt.position.y = 2.28; g.add(pt);
    const ts = new THREE.Mesh(new THREE.ConeGeometry(0.06, 0.16, 6, 1, true), wpnMat(0xb3261c, 1)); ts.position.y = 2.06; ts.rotation.x = Math.PI; g.add(ts); return g; } },
  shield: { name: '藤牌 Rattan shield + dao', hand: 'r', shield: true, build() { return WEAPON.dao.build(); } },
  bow: { name: '弓 Horn bow', hand: 'l', bow: true, build() { // a short reflex bow of horn and sinew; the string kept straight
    const g = new THREE.Group(); const pts = []; for (let i = 0; i <= 16; i++) { const t = i / 16 * 2 - 1; pts.push(new V3(-0.09 * (1 - t * t) + 0.05 * Math.pow(Math.abs(t), 3), t * 0.62, 0)); }
    g.add(new THREE.Mesh(new THREE.TubeGeometry(new THREE.CatmullRomCurve3(pts), 10, 0.015, 4), wpnMat(0x4a2a18, 0.6)));
    const str = new THREE.Mesh(new THREE.BoxGeometry(0.004, 1.24, 0.004), wpnMat(0xe8dcc0, 0.9)); str.position.x = -0.04 + 0.05; g.add(str); return g; } },
  none: { name: '無 Unarmed', hand: null, build() { return null; } },
};
function shieldMesh() { // 藤牌: a domed shield of coiled rattan, a tiger's face painted on it to frighten horses (紀效新書 藤牌)
  const c = document.createElement('canvas'); c.width = c.height = 256; const g = c.getContext('2d'); g.fillStyle = '#b48a46'; g.fillRect(0, 0, 256, 256);
  for (let r = 4; r < 130; r += 5) { g.strokeStyle = r % 10 ? 'rgba(80,50,20,.5)' : 'rgba(255,230,170,.35)'; g.lineWidth = 3; g.beginPath(); g.arc(128, 128, r, 0, 7); g.stroke(); }
  g.fillStyle = '#e0a028'; g.beginPath(); g.arc(128, 128, 70, 0, 7); g.fill(); g.fillStyle = '#1a120c';
  for (const s of [-1, 1]) { g.beginPath(); g.ellipse(128 + s * 26, 112, 14, 9, s * 0.3, 0, 7); g.fill(); g.fillStyle = '#fff4c8'; g.beginPath(); g.arc(128 + s * 26, 112, 4, 0, 7); g.fill(); g.fillStyle = '#1a120c'; }
  for (let i = -3; i <= 3; i++) { g.fillRect(118 + i * 4, 60, 3, 22 - Math.abs(i) * 4); } g.beginPath(); g.moveTo(98, 150); g.quadraticCurveTo(128, 175, 158, 150); g.lineWidth = 6; g.strokeStyle = '#1a120c'; g.stroke();
  g.fillStyle = '#f2ead8'; for (const s of [-1, 1]) { g.beginPath(); g.moveTo(128 + s * 10, 152); g.lineTo(128 + s * 16, 170); g.lineTo(128 + s * 22, 153); g.fill(); }
  const t = new THREE.CanvasTexture(c); t.encoding = THREE.sRGBEncoding;
  const geo = new THREE.SphereGeometry(0.62, 8, 3, Math.PI / 8, Math.PI * 2, 0, 0.72); geo.translate(0, -0.62 * Math.cos(0.72), 0); const uv = geo.attributes.uv, P = geo.attributes.position; for (let i = 0; i < P.count; i++) uv.setXY(i, P.getX(i) / 0.86 + 0.5, P.getZ(i) / 0.86 + 0.5);
  const m = new THREE.Mesh(geo, new THREE.MeshStandardMaterial({ map: t, roughness: 0.7, side: THREE.DoubleSide, flatShading: true })); m.castShadow = true; return m;
}
// attach a rigid object made in the bind pose's model space to a bone: the wrapper carries the bone's inverse bind matrix
function onBone(man, boneName, obj) { const w = new THREE.Group(); w.matrixAutoUpdate = false; w.matrix.copy(man.skel.boneInverses[BODY.bi[boneName]]); w.add(obj); man.bones[boneName].add(w); return w; }

// ---------------------------------------------------------------------------------------------------------------------
// a man: the shared body, cloned with its own skeleton, wearing a set and carrying a weapon
// ---------------------------------------------------------------------------------------------------------------------
class Man {
  constructor(setKey, wpnKey, scene) {
    this.root = THREE.SkeletonUtils.clone(BODY.gltf.scene); this.root.userData.man = this; this.scene = scene; scene.add(this.root);
    this.body = []; this.root.traverse(o => { if (o.isSkinnedMesh) { this.body.push(o); o.visible = false; } }); /* the mannequin's own meshes only lend their skeleton */
    this.skel = this.body[0].skeleton; this.host = this.body[0].parent; this.bones = {}; for (const b of this.skel.bones) this.bones[b.name] = b;
    this.mixer = new THREE.AnimationMixer(this.root); this.acts = {}; this.meshes = []; this.attached = [];
    this.anim = new Animator(this); this.equip(setKey); this.arm(wpnKey || 'dao');
  }
  skinned(geo, m) { const sk = new THREE.SkinnedMesh(geo, m); sk.bind(this.skel, this.body[0].bindMatrix); sk.frustumCulled = false; this.host.add(sk); this.meshes.push(sk); return sk; }
  equip(setKey) {
    this.setKey = setKey; const S = ARMOR[setKey], G = setGeo(setKey); for (const m of this.meshes) m.parent.remove(m); this.meshes = [];
    const sk = this.skinned(G.skin, solid(SKIN[S.face] || '#c8946a', 0.75)); sk.castShadow = sk.receiveShadow = true;
    for (const P of G.parts) { const m = this.skinned(P.geo, matOf(P.k)); m.castShadow = m.receiveShadow = true; }
    this.skinned(G.line, LINE); this.hidGeo = G.hid;
    for (const w of this.attached.filter(a => a.userData.headgear)) w.parent.remove(w); this.attached = this.attached.filter(a => !a.userData.headgear);
    this.faceKind = S.face; this.faceMat = new THREE.MeshStandardMaterial({ map: faceTex(S.face, 'calm'), transparent: true, roughness: 0.85, polygonOffset: true, polygonOffsetFactor: -2, depthWrite: false });
    const fw = onBone(this, 'Head', new THREE.Mesh(faceGeo(), this.faceMat)); fw.userData.headgear = true; this.attached.push(fw); this.expr = 'calm';
  }
  arm(wpnKey) {
    this.wpnKey = wpnKey; for (const w of this.attached.filter(a => a.userData.weapon)) w.parent.remove(w); this.attached = this.attached.filter(a => !a.userData.weapon);
    const W = WEAPON[wpnKey]; this.spear = null; this.shield = null;
    if (W.hand) { const F = gripFrame(W.hand), obj = W.build(); obj.matrixAutoUpdate = false; obj.matrix.copy(F.m); obj.traverse(o => { if (o.isMesh) o.castShadow = true; }); inkRigid(obj);
      const holder = new THREE.Group(); holder.add(obj); const w = onBone(this, 'hand_' + W.hand, holder); w.userData.weapon = true; this.attached.push(w); if (W.two) this.spear = { obj, holder }; }
    if (W.shield) { const sh = shieldMesh(); inkRigid(sh); const a = BODY.bpos('lowerarm_l'), b = BODY.bpos('hand_l'), F = gripFrame('l'); const back = F.palm.clone().negate();
      const holder = new THREE.Group(); holder.add(sh); holder.position.copy(a.clone().lerp(b, 0.62).add(back.clone().multiplyScalar(0.075))); holder.quaternion.setFromUnitVectors(new V3(0, 1, 0), back);
      const w = onBone(this, 'lowerarm_l', holder); w.userData.weapon = true; this.attached.push(w); this.shield = holder; }
    this.anim.armed();
  }
  setExpr(e) { if (e === this.expr) return; this.expr = e; this.faceMat.map = faceTex(this.faceKind, e); this.faceMat.needsUpdate = true; }
  update(dt) { this.anim.update(dt); }
  dispose() { this.scene.remove(this.root); this.mixer.stopAllAction(); }
}
// the ink line round a rigid piece (a weapon, a shield): its own back faces, pushed out along their normals
const RIG_LINE = new THREE.MeshBasicMaterial({ color: 0x15100b, side: THREE.BackSide });
function inkRigid(obj) { const meshes = []; obj.traverse(o => { if (o.isMesh && !o.userData.ink) meshes.push(o); });
  for (const o of meshes) { const g = o.geometry.clone(); const P = g.attributes.position, N = g.attributes.normal; if (!N) continue; for (let i = 0; i < P.count; i++) P.setXYZ(i, P.getX(i) + N.getX(i) * 0.004, P.getY(i) + N.getY(i) * 0.004, P.getZ(i) + N.getZ(i) * 0.004);
    const l = new THREE.Mesh(g, RIG_LINE); l.userData.ink = true; o.add(l); } }

// ---------------------------------------------------------------------------------------------------------------------
// the animator: the game's states on the new clips. A base layer picks the gait from speed and the direction of travel
// (forward, strafe, back; walk, jog, sprint) at a playback speed matched to the clip's own stride so the feet do not slide;
// one-shots (cuts, blocks, hits, falls) play over it and hand back. On top, procedural layers the clips do not have:
// two-handed spear work by IK (both arms solved onto the shaft), and a look-at through the chest and head.
// ---------------------------------------------------------------------------------------------------------------------
// the game's combo chains (sim.js CB) on the library's sword sets
const CHAINS = {
  lianhuan: { zh: '連環', en: 'cut, cut back, chop', steps: ['Sword_Regular_A', 'Sword_Regular_B', 'Sword_Regular_C'] },
  duanda: { zh: '短打', en: 'close work', steps: ['Sword_Light_A', 'Sword_Light_B', 'Sword_Light_C'] },
  po: { zh: '破', en: 'break the guard', steps: ['Sword_Heavy_A', 'Sword_Heavy_B'] },
  zhui: { zh: '追', en: 'the chase', steps: ['Sword_Light_Combo'] },
  fan: { zh: '反', en: 'riposte from the bind', steps: ['Sword_UpperCut'] },
  chong: { zh: '衝', en: 'the charging cut', steps: ['Sword_Dash'] },
};
const HITS = { L: 'Hit_Shoulder_L', R: 'Hit_Shoulder_R', U: 'Hit_Head', D: 'Hit_Stomach', F: 'Hit_Chest', heavy: 'Hit_Knockback' };
const IDLES = ['Idle_Loop', 'Idle_LookAround_Loop', 'Idle_Tired_Loop'];
// metres a second each gait covers, read off the root-motion versions of the libraries (UAL1_RM / UAL2_RM): exact, so the feet hold
const SPEED = { Walk_Fwd_Loop: 1.01, Jog_Fwd_Loop: 5.36, Sprint_Loop: 8.25, Sprint_Shield_Loop: 7.5, Walk_Bwd_Loop: 1.05, Jog_Bwd_Loop: 3.21, Walk_L_Loop: 0.68, Jog_Left_Loop: 3.21, Walk_R_Loop: 0.6, Jog_Right_Loop: 3.21, Crawl_Fwd_Loop: 0.6 };
const GAITS = { fwd: ['Walk_Fwd_Loop', 'Jog_Fwd_Loop', 'Sprint_Loop'], back: ['Walk_Bwd_Loop', 'Jog_Bwd_Loop'], left: ['Walk_L_Loop', 'Jog_Left_Loop'], right: ['Walk_R_Loop', 'Jog_Right_Loop'] };
// the one-shots that travel (their root motion, metres in his own frame: +x to his left, +z ahead)
const TRAVEL = { Dodge_Left: [2.0, 0], Dodge_Right: [-2.0, 0], Roll: [0, 5.0], Sword_Dash: [0, 3.7], Shield_Dash: [0, 1.0] };
class Animator {
  constructor(man) { this.man = man; this.bw = {}; this.os = []; this.one = null; this.phase = Math.random(); this.speed = 0; this.ang = 0; this.combat = false; this.idle = IDLES[(Math.random() * 3) | 0]; this.idleT = 6 + Math.random() * 8;
    this.chain = null; this.step = 0; this.pending = false; this.hold = null; this.dead = false; this.down = false; this.look = null; this.lookW = 0; this.spearT = -1; this.blockOn = false; this.cbT = 0; this.dirW = { fwd: 1, back: 0, left: 0, right: 0 }; this.pointAt = null; this.pointW = 0; this.orderT = 0; }
  A(name) { const m = this.man; if (!m.acts[name]) { const c = BODY.clips[name]; if (!c) return null; m.acts[name] = m.mixer.clipAction(c); } return m.acts[name]; }
  armed() { const k = this.man.wpnKey; this.combat = k !== 'none'; this.hands = { r: ['dao', 'shield', 'spear'].includes(k) ? 'fist' : 'relax', l: ['spear', 'shield', 'bow'].includes(k) ? 'fist' : 'relax' }; }
  // 衝: the order to charge: the weapon goes up, the off hand points the way, the head turns to it, and he shouts
  order(target, dur) { if (this.dead || this.down) return; this.pointAt = target.clone(); this.orderT = dur || 2.2; this.look = target.clone(); this.man.setExpr('shout'); }
  get base() { return this.stance(); }
  stance() { const m = this.man; if (this.hold) return this.hold; return m.shield ? 'Idle_Shield_Loop' : (this.combat && m.wpnKey !== 'none' && !m.spear && m.wpnKey !== 'bow') ? 'Sword_Idle' : (this.combat || m.spear) && this.idle === 'Idle_Tired_Loop' ? 'Idle_Loop' : this.idle; } /* a man under arms does not slouch */
  // ---- one-shots: each fades in over the base and out again; a new one takes over from the last
  play(name, o) { o = o || {}; if (this.dead && !o.force) return null; const a = this.A(name); if (!a) return null; const f = o.fade === undefined ? 0.12 : Math.max(0.02, o.fade);
    for (const e of this.os) e.target = 0, e.rate = 1 / f;
    const prev = this.os.find(e => e.a === a); if (prev) this.os = this.os.filter(e => e.a !== a); /* the same clip again: it takes over its own fading entry, which must not stop it when it fades out (that left no clip on the body: the T-pose) */
    a.reset(); a.enabled = true; a.setLoop(o.loop ? THREE.LoopRepeat : THREE.LoopOnce, Infinity); a.clampWhenFinished = true; a.timeScale = o.ts || 1; a.setEffectiveWeight(0); a.play();
    this.os.push({ a, w: prev ? prev.w * 0.5 : 0, target: 1, rate: 1 / f }); this.one = { name, a, then: o.then === undefined ? null : o.then, chainAt: o.chainAt || 0.62, attack: !!o.attack, freezeAt: o.freezeAt, hold: !!o.hold || !!o.loop };
    if (o.expr) this.man.setExpr(o.expr); return a; }
  endOne() { for (const e of this.os) { e.target = 0; e.rate = 1 / 0.18; } this.one = null; }
  attack(key) {
    if (this.dead || this.down || this.man.wpnKey === 'none' || this.man.wpnKey === 'bow') return; if (this.man.spear) return this.thrust();
    const one = this.one; this.combat = true; this.cbT = 4;
    if (one && one.attack) { const p = one.a.time / one.a.getClip().duration; const C = CHAINS[this.chain];
      if (key === this.chain && this.step + 1 < C.steps.length) { if (p >= one.chainAt) return this.chainStep(this.step + 1, 0.1); this.pending = true; return; } if (p < 0.85) { this.pending = false; return; } }
    this.chain = CHAINS[key] ? key : 'lianhuan'; this.chainStep(0, 0.12);
  }
  chainStep(i, fade) { const C = CHAINS[this.chain]; this.step = i; this.pending = false; const name = C.steps[i];
    this.play(name, { fade, attack: true, expr: 'shout', then: () => { if (this.pending && this.step + 1 < C.steps.length) return this.chainStep(this.step + 1, 0.08); const r = BODY.clips[name + '_Rec'] ? name + '_Rec' : null; this.chain = null; if (r) this.play(r, { fade: 0.08, expr: 'calm' }); else { this.man.setExpr('calm'); this.endOne(); } } }); }
  thrust() { if (this.spearT >= 0 && this.spearT < 0.45) return; this.spearT = 0; this.combat = true; this.man.setExpr('shout'); }
  block(on) { if (this.dead || this.down) return; if (on && !this.blockOn) { this.blockOn = true; if (this.man.spear) return; this.play(this.man.shield ? 'Idle_Shield_Break' : 'Sword_Block', { fade: 0.08, freezeAt: this.man.shield ? 0.18 : 0.42, hold: true }); }
    else if (!on && this.blockOn) { this.blockOn = false; if (this.one && this.one.hold) this.endOne(); } }
  hit(dir, heavy) { if (this.dead || this.down) return; this.blockOn = false; this.chain = null; this.pending = false; this.play(heavy ? HITS.heavy : (HITS[dir] || HITS.F), { fade: 0.06, expr: 'pain', then: () => { this.man.setExpr('calm'); this.endOne(); } }); }
  die() { this.blockOn = false; this.chain = null; this.dead = true; this.play(Math.random() < 0.5 ? 'Death01' : 'Death02', { fade: 0.1, force: true, expr: 'pain', then: () => {} }); }
  wound() { this.dead = false; this.down = true; this.play('IdleToLay', { fade: 0.15, force: true, expr: 'pain', then: () => {} }); }
  rise() { if (!this.down) return; this.play('LayToIdle', { fade: 0.15, force: true, expr: 'calm', then: () => { this.down = false; this.endOne(); } }); }
  revive() { this.dead = false; this.down = false; this.hold = null; this.blockOn = false; this.chain = null; this.man.setExpr('calm'); this.endOne(); }
  // ---- per frame: the base is a blend (stance and the two gaits either side of his speed, in the direction he travels, all on one
  // phase so the feet agree); one-shots lie over it; every weight is normalised so nothing ever blends toward the bind pose
  update(dt) {
    const m = this.man; if (this.cbT > 0) { this.cbT -= dt; if (this.cbT <= 0 && !this.blockOn) this.combat = m.wpnKey !== 'none' && !!this.keepCombat; }
    if (this.one) { const a = this.one.a, dur = a.getClip().duration;
      if (this.one.freezeAt !== undefined && this.blockOn && a.time >= dur * this.one.freezeAt) a.timeScale = 0;
      if (!this.one.hold && a.time >= dur - 0.03) { const then = this.one.then; this.one = null; if (then) then(); else this.endOne(); } }
    let oneW = 0; for (const e of this.os) { e.w += clamp(e.target - e.w, -e.rate * dt, e.rate * dt); oneW += e.w; }
    this.os = this.os.filter(e => { if (e.target === 0 && e.w <= 0.001) { if (!this.os.some(o => o !== e && o.a === e.a)) e.a.stop(); return false; } return true; });
    // the base
    const tgt = {}, sp = this.speed, ang = this.ang, loco = clamp((sp - 0.08) / 0.45, 0, 1); const st = this.stance(); tgt[st] = 1 - loco;
    const dir = Math.abs(ang) > 2.3 ? 'back' : ang > 0.8 ? 'left' : ang < -0.8 ? 'right' : 'fwd'; for (const d in this.dirW) this.dirW[d] += ((d === dir ? 1 : 0) - this.dirW[d]) * Math.min(1, dt * 7);
    let period = 0, pw = 0;
    for (const d in this.dirW) { const w0 = this.dirW[d] * loco; if (w0 < 0.002) continue; const G = GAITS[d].filter(n => BODY.clips[n]), v = G.map(n => SPEED[n]); let k = 0; while (k < G.length - 2 && sp > v[k + 1]) k++;
      const t = G.length > 1 ? clamp((sp - v[k]) / (v[k + 1] - v[k]), 0, 1) : 0; const a = G[k], b = G[Math.min(k + 1, G.length - 1)];
      tgt[a] = (tgt[a] || 0) + w0 * (1 - t); if (b !== a) tgt[b] = (tgt[b] || 0) + w0 * t;
      const pa = BODY.clips[a].duration, pb = BODY.clips[b].duration; const vt = lerp(v[k], v[Math.min(k + 1, G.length - 1)], t) || 1; const P = lerp(pa, pb, t) * clamp(vt / Math.max(sp, 0.3), 0.5, 2.5); period += P * w0; pw += w0; }
    if (pw > 0) this.phase = (this.phase + dt / (period / pw)) % 1;
    for (const n in tgt) if (!(n in this.bw)) this.bw[n] = 0;
    let sum = 0; for (const n in this.bw) { const g = tgt[n] || 0; this.bw[n] += (g - this.bw[n]) * Math.min(1, dt * 9); if (this.bw[n] < 0.002 && !g) { const a = this.A(n); a.stop(); delete this.bw[n]; continue; } sum += this.bw[n]; }
    const baseShare = Math.max(0, 1 - Math.min(1, oneW)), norm = sum > 0 ? baseShare / sum : 0, oneNorm = oneW > 1 ? 1 / oneW : 1;
    for (const n in this.bw) { const a = this.A(n); if (!a.isRunning()) { a.reset(); a.setLoop(THREE.LoopRepeat, Infinity); a.play(); } a.setEffectiveWeight(this.bw[n] * norm);
      if (SPEED[n]) { a.timeScale = 0; a.time = this.phase * a.getClip().duration; } else a.timeScale = 1; }
    for (const e of this.os) e.a.setEffectiveWeight(e.w * oneNorm);
    { let tot = 0; for (const a of m.mixer._actions) if (a.isRunning() || (a.enabled && a.paused)) tot += a.getEffectiveWeight(); /* never less than a whole body: whatever is missing the stance fills, so no frame falls back to the bind pose */
      if (tot < 0.995) { const a = this.A(st); if (!a.isRunning()) { a.reset(); a.setLoop(THREE.LoopRepeat, Infinity); a.play(); } a.setEffectiveWeight(a.getEffectiveWeight() + 1 - tot); this.bw[st] = this.bw[st] || 0.001; } }
    if (IDLES.includes(st) && loco < 0.5) { this.idleT -= dt; if (this.idleT <= 0) { this.idleT = 8 + Math.random() * 9; this.idle = IDLES[(IDLES.indexOf(this.idle) + 1 + ((Math.random() * 2) | 0)) % IDLES.length]; } }
    m.mixer.update(dt); m.root.updateMatrixWorld(true);
    if (this.hands) { const pt = this.pointW > 0.4; poseHand(m, 'r', this.hands.r, 1); poseHand(m, 'l', pt ? 'point' : this.hands.l, 1); }
    if (m.spear && !this.dead && !this.down) this.spearIK(dt);
    if (this.orderT > 0) { this.orderT -= dt; if (this.orderT <= 0) { this.pointAt = null; this.look = null; this.man.setExpr('calm'); } }
    this.pointW += ((this.pointAt && !this.dead && !this.down ? 1 : 0) - this.pointW) * Math.min(1, dt * 7);
    if (this.pointW > 0.01 && (this.pointAt || this.lastPoint)) { if (this.pointAt) this.lastPoint = this.pointAt; const w = sm(this.pointW);
      const S = m.bones.upperarm_l.getWorldPosition(new V3()), d = this.lastPoint.clone().sub(S); d.y = Math.max(d.y, 0.05 * d.length()); aimArm(m, 'l', d, w, 0.03); /* the off hand points the way, a little above the line */
      if (m.wpnKey !== 'none' && m.wpnKey !== 'bow') { const fwd = new V3(0, 0, 1).applyQuaternion(m.root.quaternion); aimArm(m, 'r', fwd.clone().multiplyScalar(0.35).add(new V3(0, 1, 0)), w * 0.9, 0.12); } } /* the weapon raised high */
    if (this.look && !this.dead && !this.down) this.lookAt(dt);
  }
  // ---- two-handed spear: the shaft is placed by the body (rear hand at the right hip, front hand ahead on the centre line,
  // point at chest height), driven out and back for a thrust, and both arms are solved onto it
  spearIK(dt) {
    const m = this.man, R = m.root, fwd = new V3(0, 0, 1).applyQuaternion(R.quaternion), left = new V3(1, 0, 0).applyQuaternion(R.quaternion), up = new V3(0, 1, 0);
    let k = 0; if (this.spearT >= 0) { this.spearT += dt; const t = this.spearT; k = t < 0.18 ? -0.35 * sm(t / 0.18) : t < 0.32 ? lerp(-0.35, 1, sm((t - 0.18) / 0.14)) : t < 0.7 ? lerp(1, 0, sm((t - 0.32) / 0.38)) : 0; if (t > 0.75) { this.spearT = -1; m.setExpr('calm'); } }
    const pel = m.bones.pelvis.getWorldPosition(new V3()), dir = fwd.clone().multiplyScalar(0.96).add(up.clone().multiplyScalar(0.06)).normalize(), push = dir.clone().multiplyScalar(k * 0.4);
    const rear = pel.clone().add(left.clone().multiplyScalar(-0.29)).add(fwd.clone().multiplyScalar(-0.03)).add(up.clone().multiplyScalar(0.13)).add(push); /* the rear hand out at the right hip, clear of the coat */
    const front = rear.clone().add(dir.clone().multiplyScalar(0.33)).add(left.clone().multiplyScalar(0.25)).add(up.clone().multiplyScalar(0.04)); /* the lead hand ahead of the belly, within the left arm's reach */
    const sd = front.clone().sub(rear).normalize();
    ik2(m.bones.upperarm_r, m.bones.lowerarm_r, m.bones.hand_r, rear, rear.clone().add(left.clone().multiplyScalar(-0.7)).add(up.clone().multiplyScalar(0.05)).add(fwd.clone().multiplyScalar(-0.45))); /* the elbow out and back, never in across the body */
    handTo(m, 'r', sd, up.clone().multiplyScalar(-0.6).add(left.clone().multiplyScalar(-0.4)).normalize());
    ik2(m.bones.upperarm_l, m.bones.lowerarm_l, m.bones.hand_l, front, front.clone().add(left.clone().multiplyScalar(0.8)).add(up.clone().multiplyScalar(-0.25)));
    handTo(m, 'l', sd, up.clone().multiplyScalar(-0.7).add(left.clone().multiplyScalar(0.3)).normalize());
    if (k > 0) { const sp = m.bones.spine_02; const q = new Q().setFromAxisAngle(up, -0.35 * k); rotWorld(sp, q); } /* the hips and trunk turn into the thrust */
  }
  lookAt(dt) { // the chest and the head turn toward what he is watching (yaw only), sharing the turn
    const m = this.man, fwd = new V3(0, 0, 1).applyQuaternion(m.root.quaternion), hp = m.bones.Head.getWorldPosition(new V3()), to = this.look.clone().sub(hp); to.y = 0; if (to.lengthSq() < 0.01) return; to.normalize();
    let a = Math.atan2(fwd.x * to.z - fwd.z * to.x, fwd.x * to.x + fwd.z * to.z); a = clamp(-a, -0.9, 0.9); this.lookW += ((this.one && this.one.attack ? 0.3 : 1) - this.lookW) * Math.min(1, dt * 5);
    const up = new V3(0, 1, 0); rotWorld(m.bones.spine_03, new Q().setFromAxisAngle(up, a * 0.35 * this.lookW)); rotWorld(m.bones.Head, new Q().setFromAxisAngle(up, a * 0.6 * this.lookW));
  }
}
// ---- hands: every frame the fingers are set to a pose (a fist round a grip, relaxed, open, pointing): the library's
// fingers were made for a round hand, and blocks need a clean closed fist or they read as a claw
const FINGERS = ['index', 'middle', 'ring', 'pinky'];
const HANDPOSE = { fist: { f: [1.3, 1.5, 1.05], t: [0.35, 0.55, 0.5] }, relax: { f: [0.35, 0.5, 0.35], t: [0.15, 0.2, 0.15] }, open: { f: [0.05, 0.08, 0.05], t: [0.0, 0.05, 0.05] },
  point: { f: [1.3, 1.5, 1.05], t: [0.35, 0.55, 0.5], index: [0.0, 0.04, 0.02] } };
function curlAxes(side) { const k = 'curl' + side; if (BODY[k]) return BODY[k]; const F = gripFrame(side), out = {};
  const A = new V3().crossVectors(F.fd, F.palm).normalize(); const tdir = BODY.bpos('thumb_02_' + side).sub(BODY.bpos('thumb_01_' + side)).normalize(), At = new V3().crossVectors(F.palm, tdir).normalize(); /* the thumb folds across the palm, toward the little finger */
  for (const f of FINGERS.concat(['thumb'])) for (let i = 1; i <= 3; i++) { const n = f + '_0' + i + '_' + side, R = new M4().extractRotation(BODY.bindWorld[BODY.bi[n]]).invert(); out[n] = (f === 'thumb' ? At : A).clone().applyMatrix4(R).normalize(); }
  return (BODY[k] = out); }
function poseHand(m, side, pose, w) { const P = HANDPOSE[pose], ax = curlAxes(side), q = new Q();
  for (const f of FINGERS.concat(['thumb'])) for (let i = 1; i <= 3; i++) { const n = f + '_0' + i + '_' + side, bone = m.bones[n], th = f === 'thumb' ? P.t[i - 1] : (f === 'index' && P.index ? P.index[i - 1] : P.f[i - 1]);
    q.copy(BODY.restQ[n]).multiply(new Q().setFromAxisAngle(ax[n], th)); if (w >= 0.999) bone.quaternion.copy(q); else bone.quaternion.slerp(q, w); } }
// aim a chain (upper arm, forearm, hand) along a direction from the shoulder, blended over the animation by w
function aimArm(m, side, dirW, w, bendUp) { const U = m.bones['upperarm_' + side], L = m.bones['lowerarm_' + side], H = m.bones['hand_' + side], save = [U, L, H].map(b => b.quaternion.clone());
  const S = U.getWorldPosition(new V3()), l1 = S.distanceTo(L.getWorldPosition(new V3())), l2 = L.getWorldPosition(new V3()).distanceTo(H.getWorldPosition(new V3())), d = dirW.clone().normalize();
  const e = S.clone().add(d.clone().multiplyScalar(l1)).add(new V3(0, bendUp || 0, 0)); aimBone(U, L.getWorldPosition(new V3()), e);
  aimBone(L, H.getWorldPosition(new V3()), e.clone().add(d.clone().multiplyScalar(l2))); aimBone(H, m.bones['middle_01_' + side].getWorldPosition(new V3()), H.getWorldPosition(new V3()).add(d));
  if (w < 0.999) { [U, L, H].forEach((b, i) => { const q = b.quaternion.clone(); b.quaternion.copy(save[i]).slerp(q, w); }); U.updateMatrixWorld(true); } }
// rotate a bone by a world-space rotation, keeping its parent: local' = parentWorld⁻¹ · q · world
const _q1 = new Q(), _q2 = new Q(), _v1 = new V3(), _v2 = new V3(), _v3 = new V3();
function rotWorld(bone, q) { bone.getWorldQuaternion(_q1); _q1.premultiply(q); bone.parent.getWorldQuaternion(_q2); bone.quaternion.copy(_q2.invert().multiply(_q1)); bone.updateMatrixWorld(true); }
function aimBone(bone, childNow, want) { const p = bone.getWorldPosition(new V3()), a = childNow.clone().sub(p).normalize(), b = want.clone().sub(p).normalize(); if (a.dot(b) > 0.99999) return; rotWorld(bone, new Q().setFromUnitVectors(a, b)); }
// analytic two-bone IK: the elbow placed by the law of cosines in the plane of shoulder, target and pole
function ik2(up, lo, hand, target, pole) {
  const A = up.getWorldPosition(new V3()), B = lo.getWorldPosition(new V3()), C = hand.getWorldPosition(new V3()); const l1 = A.distanceTo(B), l2 = B.distanceTo(C);
  const d = clamp(A.distanceTo(target), 0.01, l1 + l2 - 0.002), dir = target.clone().sub(A).normalize(); let pd = pole.clone().sub(A); pd.sub(dir.clone().multiplyScalar(pd.dot(dir))); if (pd.lengthSq() < 1e-8) pd.set(0, -1, 0); pd.normalize();
  const ca = clamp((l1 * l1 + d * d - l2 * l2) / (2 * l1 * d), -1, 1), sa = Math.sqrt(1 - ca * ca); const elbow = A.clone().add(dir.clone().multiplyScalar(l1 * ca)).add(pd.multiplyScalar(l1 * sa));
  aimBone(up, B, elbow); aimBone(lo, hand.getWorldPosition(new V3()), A.clone().add(dir.multiplyScalar(d)));
}
// turn a hand so its grip axis (thumb side) lies along a direction, its knuckles toward another
function handTo(m, side, axisW, knuckW) {
  const F = gripFrame(side), bi = BODY.bi['hand_' + side], Rb = new M4().extractRotation(BODY.bindWorld[bi]).invert();
  const aL = F.across.clone().applyMatrix4(Rb).normalize(), fL = F.fd.clone().applyMatrix4(Rb).normalize(); fL.sub(aL.clone().multiplyScalar(fL.dot(aL))).normalize();
  const aW = axisW.clone().normalize(), fW = knuckW.clone().sub(aW.clone().multiplyScalar(knuckW.dot(aW))).normalize();
  const L = new M4().makeBasis(fL, aL, new V3().crossVectors(fL, aL)), W = new M4().makeBasis(fW, aW, new V3().crossVectors(fW, aW));
  const qW = new Q().setFromRotationMatrix(W.multiply(L.transpose())); const bone = m.bones['hand_' + side]; bone.parent.getWorldQuaternion(_q2); bone.quaternion.copy(_q2.invert().multiply(qW)); bone.updateMatrixWorld(true);
}
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
function clear() { for (const m of men) m.dispose(); men = []; sel = null; duel = null; file = null; check = null; }
function setMode(mm) {
  mode = mm; clear(); for (const b of document.querySelectorAll('#modes button')) b.classList.toggle('on', b.dataset.m === mm);
  if (mm === 'show' || mm === 'check') { const m = new Man(cur.set, cur.wpn, scene); mover(m, 0, 0, 0); men.push(m); sel = m; camera.position.set(1.5, 1.5, 3.6); orbit.target.set(0, 1.0, 0); if (mm === 'check') startCheck(); }
  if (mm === 'lineup') { const keys = Object.keys(ARMOR).filter(k => k !== 'bare'), W = ['dao', 'spear', 'shield', 'dao', 'dao', 'spear', 'bow', 'dao']; keys.forEach((k, i) => { const m = new Man(k, W[i % W.length], scene); mover(m, (i - (keys.length - 1) / 2) * 1.3, 0, 0); men.push(m); }); sel = men[0]; camera.position.set(0, 2.2, 9.5); orbit.target.set(0, 1.0, 0); }
  if (mm === 'duel') startDuel();
  if (mm === 'file') startFile();
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
      const p = A.one.a.time / A.one.a.getClip().duration; if (!A.one.landed && p > 0.4) { A.one.landed = true; if (d < 1.9 && !o.anim.dead) { if (o.anim.blockOn) { spark(o); } else { o.hp--; o.anim.hit(STRIKE[A.one.name] || 'F', A.one.name.includes('Heavy') && o.hp <= 1); if (o.hp <= 0) setTimeout(() => { o.anim.die(); m.anim.keepCombat = false; duel.over = 6; setTimeout(() => { if (!m.anim.dead) m.anim.play('Celebration', { fade: 0.3, expr: 'shout' }); }, 1500); }, 250); } } } continue; }
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
    ['Order: charge! (point)', each(m => { const f = new V3(Math.sin(m.mv.yaw + 0.35), 0, Math.cos(m.mv.yaw + 0.35)); m.anim.order(m.root.position.clone().add(f.multiplyScalar(8)).add(new V3(0, 0.5, 0)), 2.4); })], ['Look at me', each(m => { m.anim.look = m.anim.look ? null : camera.position; })], ['Combat stance', each(m => { m.anim.combat = !m.anim.combat; m.anim.keepCombat = m.anim.combat; })],
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
  duelThink(dt); fileThink(dt);
  if (check && !check.pause) { check.t += dt; const m = men[0], name = m.clipName, c = BODY.clips[name]; if (c && check.t > Math.max(2.4, c.duration * 2)) { check.t = 0; check.i = (check.i + 1) % CLIPS().length; playClip(m, CLIPS()[check.i], true); } }
  for (const m of men) { stepMover(m, dt); m.update(dt); }
  if (mode === 'show' && men[0]) { const p = men[0].root.position; orbit.target.lerp(new V3(p.x, 1.0, p.z), Math.min(1, dt * 3)); }
  sun.position.set(orbit.target.x + 5, 9, orbit.target.z + 6); sun.target.position.copy(orbit.target);
  orbit.update(); renderer.render(scene, camera);
  if (!window.LAB.lastMeasure || mode !== 'check') { const info = renderer.info.render, s = sel || men[0]; $('stats').textContent = `fps ${fpsA.toFixed(0)}\ndraw calls ${info.calls}\ntriangles ${(info.triangles / 1000).toFixed(1)}k\nmen ${men.length}\n` + (s ? `\n${ARMOR[s.setKey].name}\n${WEAPON[s.wpnKey].name}\nclip ${s.anim.one ? s.anim.one.name : s.anim.base || ''}${s.anim.chain ? '\nchain ' + CHAINS[s.anim.chain].zh + ' ' + (s.anim.step + 1) + '/' + CHAINS[s.anim.chain].steps.length : ''}` : ''); }
  if (!Qs.has('noloop')) requestAnimationFrame(frame);
}
window.LAB = { get BODY() { return BODY; }, setMode, measureAll, get men() { return men; }, renderer, scene, camera, orbit, ARMOR, WEAPON, CHAINS, SPEED, step: (dt) => { for (const m of men) { stepMover(m, dt); m.update(dt); } duelThink(dt); fileThink(dt); orbit.update(); renderer.render(scene, camera); }, countRed, overlay };
new THREE.GLTFLoader().load('man.glb', (g) => {
  analyse(g); resize(); setMode(Qs.get('mode') || 'show'); $('load').remove(); window.LAB.ready = true; requestAnimationFrame((t) => { last = t; frame(t); });
}, undefined, (err) => { $('load').textContent = 'could not load the model: ' + (err && err.message || err); window.LAB.error = String(err && err.message || err); });
})();
