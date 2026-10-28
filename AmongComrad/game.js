(()=>{
'use strict';
// ================= deterministic math =================
// Lockstep needs every browser to compute bit-identical results. + - * / and sqrt are exact IEEE in every engine,
// but Math.sin/cos/atan2/hypot may differ in the last bit between Chrome, Firefox and Safari. These replacements
// use only exact operations, so the simulation is the same everywhere. Sign of zero is ignored on purpose.
const NM=globalThis.Math;
const HP1=1.5707963267341256,HP2=6.077100506506192e-11;
function sinP(r){const z=r*r;return r+r*z*(-1/6+z*(1/120+z*(-1/5040+z*(1/362880+z*(-1/39916800+z*(1/6227020800))))))}
function cosP(r){const z=r*r;return 1+z*(-0.5+z*(1/24+z*(-1/720+z*(1/40320+z*(-1/3628800+z*(1/479001600+z*(-1/87178291200)))))))}
function reduce(x){const k=NM.round(x/1.5707963267948966);return [(x-k*HP1)-k*HP2,((k%4)+4)%4]}
function fsin(x){if(!isFinite(x))return NaN;const [r,q]=reduce(x);return q===0?sinP(r):q===1?cosP(r):q===2?-sinP(r):-cosP(r)}
function fcos(x){if(!isFinite(x))return NaN;const [r,q]=reduce(x);return q===0?cosP(r):q===1?-sinP(r):q===2?-cosP(r):sinP(r)}
function fatanS(x){// |x|<=1
  let n=0;while(x>0.13||x<-0.13){x=x/(1+NM.sqrt(1+x*x));n++}
  const z=x*x;let s=0;for(let k=23;k>=1;k-=2)s=1/k-z*s;s=x*(s);return s*(1<<n)}
function fatan(x){if(x>1)return 1.5707963267948966-fatanS(1/x);if(x<-1)return -1.5707963267948966-fatanS(1/x);return fatanS(x)}
function fatan2(y,x){if(x===0){if(y===0)return 0;return y>0?1.5707963267948966:-1.5707963267948966}
  if(y===0)return x>0?0:3.141592653589793;const a=fatan(y/x);if(x>0)return a;return y>0?a+3.141592653589793:a-3.141592653589793}
const Math=Object.assign(Object.create(NM),{sin:fsin,cos:fcos,atan2:fatan2,hypot:(x,y)=>NM.sqrt(x*x+y*y)});
// ================= utils =================
// rnd: seeded game-logic RNG (identical on every peer). crnd: cosmetic only (smoke, sparks, sound) — never touches game state.
let RS=1;
function rnd(){RS=RS+0x6D2B79F5|0;let t=Math.imul(RS^RS>>>15,1|RS);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}
const crnd=NM.random;
const clamp=(v,a,b)=>v<a?a:v>b?b:v,pick=a=>a[Math.floor(rnd()*a.length)],TAU=Math.PI*2;
const dist=(ax,ay,bx,by)=>Math.hypot(ax-bx,ay-by);
function shuffle(a){for(let i=a.length-1;i>0;i--){const j=Math.floor(rnd()*(i+1));[a[i],a[j]]=[a[j],a[i]]}return a}
function mulberry(a){return function(){a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296}}
function angDiff(a,b){let d=(b-a)%TAU;if(d>Math.PI)d-=TAU;if(d<-Math.PI)d+=TAU;return d}
function rr(g,x,y,w,h,r){r=Math.min(r,w/2,h/2);g.beginPath();g.moveTo(x+r,y);g.arcTo(x+w,y,x+w,y+h,r);g.arcTo(x+w,y+h,x,y+h,r);g.arcTo(x,y+h,x,y,r);g.arcTo(x,y,x+w,y,r);g.closePath()}
const $=id=>document.getElementById(id);
const esc=s=>String(s).replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const REDUCED=matchMedia('(prefers-reduced-motion: reduce)').matches;
const TOUCH=matchMedia('(pointer: coarse)').matches;
const listNames=a=>a.length<=1?(a[0]||''):a.slice(0,-1).join(', ')+' and '+a[a.length-1];

// ================= map =================
const W=64,H=40;
const GROUND=0,WALL=1,COVER=2,FLOOR=3,WATER=4,WIN=5,CRATE=6;
const grid=new Uint8Array(W*H),ck=new Uint8Array(W*H);
const get=(x,y)=>(x<0||y<0||x>=W||y>=H)?WALL:grid[y*W+x];
const set=(x,y,v,k=0)=>{if(x>=0&&y>=0&&x<W&&y<H){grid[y*W+x]=v;ck[y*W+x]=k}};
function fill(x0,y0,x1,y1,v,k=0){for(let y=y0;y<=y1;y++)for(let x=x0;x<=x1;x++)set(x,y,v,k)}
const passable=(x,y)=>{const t=get(x,y);return t===GROUND||t===FLOOR};
(function buildMap(){
  const R=mulberry(1942);
  fill(60,0,63,39,WATER);
  const edge=(x,y)=>{const r=R();if(r<0.6)set(x,y,WALL);else if(r<0.8)set(x,y,COVER,2);else set(x,y,FLOOR)};
  const ruin=(x0,y0,x1,y1)=>{fill(x0,y0,x1,y1,FLOOR);for(let x=x0;x<=x1;x++){edge(x,y0);edge(x,y1)}for(let y=y0;y<=y1;y++){edge(x0,y);edge(x1,y)}for(let i=0;i<3;i++)set(x0+1+(R()*(x1-x0-1)|0),y0+1+(R()*(y1-y0-1)|0),COVER,2)};
  ruin(4,3,12,11);ruin(2,27,10,35);ruin(14,5,18,12);ruin(13,26,18,33);ruin(1,13,6,16);
  for(let y=18;y<=22;y++)for(let x=0;x<=41;x++)set(x,y,GROUND);
  for(let i=0;i<20;i++){let x=20+(R()*16|0),y=1+(R()*38|0);if(y>=16&&y<=24)continue;const n=2+(R()*3|0);for(let k=0;k<n;k++){set(x,y,COVER,2);if(R()<0.5)x+=R()<0.5?1:-1;else y+=R()<0.5?1:-1;x=clamp(x,20,35);y=clamp(y,1,38);if(y>=17&&y<=23)break}}
  fill(23,10,25,10,COVER,3);fill(27,30,29,30,COVER,3);fill(31,25,32,26,COVER,3);fill(21,23,22,23,COVER,2);fill(26,16,27,16,COVER,2);
  fill(38,2,38,8,COVER,1);fill(38,31,38,37,COVER,1);
  fill(42,9,52,30,FLOOR);
  for(let x=42;x<=52;x++){set(x,9,WALL);set(x,30,WALL)}for(let y=9;y<=30;y++){set(42,y,WALL);set(52,y,WALL)}
  for(const y of [11,12,15,16,23,24,27,28])set(42,y,WIN);
  for(const x of [44,45,49,50]){set(x,9,WIN);set(x,30,WIN)}
  for(const y of [13,14,25,26])set(52,y,FLOOR);
  for(let y=10;y<=29;y++)if(![13,14,24,25].includes(y))set(47,y,WALL);
  for(let x=43;x<=51;x++)if(![44,45,49,50].includes(x))set(x,19,WALL);
  set(45,17,COVER,2);set(50,21,COVER,2);
  set(51,11,CRATE,4);set(51,28,CRATE,4);
  for(let x=54;x<=57;x++){set(x,16,COVER,1);set(x,23,COVER,1)}for(let y=16;y<=23;y++){set(54,y,COVER,1);set(57,y,COVER,1)}
  fill(55,17,56,22,FLOOR);set(57,19,GROUND);set(57,20,GROUND);set(55,17,CRATE,4);set(55,22,CRATE,4);
})();
const CRATES=[];for(let y=0;y<H;y++)for(let x=0;x<W;x++)if(grid[y*W+x]===CRATE)CRATES.push({x:x+0.5,y:y+0.5});
const ZONES=[
 {n:'Command dugout',x0:54,y0:16,x1:57,y1:23},{n:'Volga bank',x0:57,y0:0,x1:63,y1:39},
 {n:'North windows',x0:42,y0:9,x1:46,y1:18},{n:'Stairwell',x0:47,y0:9,x1:52,y1:18},
 {n:'South windows',x0:42,y0:19,x1:46,y1:30},{n:'Back rooms',x0:47,y0:19,x1:52,y1:30},
 {n:'North trench',x0:37,y0:0,x1:41,y1:8},{n:'South trench',x0:37,y0:31,x1:41,y1:39},
 {n:'Courtyard',x0:42,y0:0,x1:56,y1:39},{n:'Front of the building',x0:37,y0:9,x1:41,y1:30},
 {n:"No-man's land",x0:19,y0:0,x1:36,y1:39},{n:'German side',x0:0,y0:0,x1:18,y1:39}];
function zoneAt(x,y){x|=0;y|=0;for(const z of ZONES)if(x>=z.x0&&x<=z.x1&&y>=z.y0&&y<=z.y1)return z.n;return 'line'}
const SOV_ZONES=['North windows','Stairwell','South windows','Back rooms','North trench','South trench','Courtyard','Command dugout'];
const POSTS=[
 ...[11,12,15,16,23,24,27,28].map(y=>({x:43.5,y:y+0.5,c:'win',face:Math.PI})),
 {x:44.5,y:10.5,c:'side',face:-Math.PI*0.72},{x:49.5,y:10.5,c:'side',face:-Math.PI/2},{x:44.5,y:29.5,c:'side',face:Math.PI*0.72},{x:49.5,y:29.5,c:'side',face:Math.PI/2},
 ...[3,5,7].map(y=>({x:39.5,y:y+0.5,c:'ntr',face:Math.PI})),...[32,34,36].map(y=>({x:39.5,y:y+0.5,c:'str',face:Math.PI})),{x:55.5,y:19.5,c:'dug',face:0},{x:56.5,y:20.5,c:'dug',face:0}];
const CSPOTS=[];for(let y=0;y<H;y++)for(let x=1;x<=37;x++){if(!passable(x,y))continue;const e=get(x+1,y);if(e===COVER||e===WALL||e===WIN)CSPOTS.push({x:x+0.5,y:y+0.5,res:null})}
const ASSAULT=[{x:55.5,y:19.5},{x:49.5,y:14.5},{x:49.5,y:25.5},{x:40.5,y:5.5},{x:40.5,y:34.5},{x:55.5,y:20.5}];
const FIRES=[{x:7.5,y:6.5},{x:16.5,y:9},{x:5.5,y:31.5},{x:24.5,y:10.5},{x:28.5,y:30.5},{x:15.5,y:30},{x:3.5,y:14.5},{x:31.5,y:25.5}];
const FIRES0=FIRES.length;

function los(ax,ay,bx,by,step){const d=Math.hypot(bx-ax,by-ay);const n=Math.ceil(d/(step||0.25));for(let i=1;i<n;i++){const x=ax+(bx-ax)*i/n,y=ay+(by-ay)*i/n;if(x<0||y<0||x>=W||y>=H)return false;if(grid[(y|0)*W+(x|0)]===WALL)return false}return true}
function blockedAt(x,y,r){return !passable(Math.floor(x-r),Math.floor(y-r))||!passable(Math.floor(x+r),Math.floor(y-r))||!passable(Math.floor(x-r),Math.floor(y+r))||!passable(Math.floor(x+r),Math.floor(y+r))}
function clearLine(ax,ay,bx,by){const d=dist(ax,ay,bx,by);const n=Math.ceil(d/0.2);for(let i=1;i<=n;i++){const x=ax+(bx-ax)*i/n,y=ay+(by-ay)*i/n;if(blockedAt(x,y,0.3))return false}return true}
const DIR4=[[1,0],[-1,0],[0,1],[0,-1]];
const prevB=new Int32Array(W*H),qB=new Int32Array(W*H);
function bfs(sx,sy,tx,ty){
  if(!passable(tx,ty))return null;
  if(!passable(sx,sy)){let f=false;for(const [dx,dy] of DIR4)if(passable(sx+dx,sy+dy)){sx+=dx;sy+=dy;f=true;break}if(!f)return null}
  prevB.fill(-1);const s=sy*W+sx,g=ty*W+tx;let h=0,t=0;qB[t++]=s;prevB[s]=s;
  while(h<t){const c=qB[h++];if(c===g)break;const cx=c%W,cy=(c/W)|0;for(const [dx,dy] of DIR4){const nx=cx+dx,ny=cy+dy;if(!passable(nx,ny))continue;const n=ny*W+nx;if(prevB[n]!==-1)continue;prevB[n]=c;qB[t++]=n}}
  if(prevB[g]===-1)return null;const p=[];let c=g;while(c!==s){p.push(c);c=prevB[c]}p.reverse();return p.map(c=>({x:c%W+0.5,y:((c/W)|0)+0.5}))}
function smooth(sx,sy,path){const out=[];let cx=sx,cy=sy,i=0;while(i<path.length){let j=Math.min(path.length-1,i+12);while(j>i&&!clearLine(cx,cy,path[j].x,path[j].y))j--;out.push(path[j]);cx=path[j].x;cy=path[j].y;i=j+1}return out}
function goTo(u,x,y){const p=bfs(u.x|0,u.y|0,x|0,y|0);if(!p){u.path=[];return false}if(p.length)p[p.length-1]={x,y};else p.push({x,y});u.path=smooth(u.x,u.y,p);return true}
function followPath(u,dt,sp){let rem=sp*dt;u.moving=u.path.length>0;while(rem>0&&u.path.length){const n=u.path[0];const dx=n.x-u.x,dy=n.y-u.y;const d=Math.hypot(dx,dy);if(d<=rem){u.x=n.x;u.y=n.y;u.path.shift();rem-=d}else{u.x+=dx/d*rem;u.y+=dy/d*rem;rem=0;u.moveA=Math.atan2(dy,dx)}}if(u.moving)u.phase+=dt*10}
function moveFree(u,dx,dy){const r=0.3;const nx=u.x+dx;if(!blockedAt(nx,u.y,r))u.x=nx;const ny=u.y+dy;if(!blockedAt(u.x,ny,r))u.y=ny}

// ================= weapons & cast =================
const WPN={
 ppsh:{name:'PPSh-41',cal:'7.62×25 mm',dmg:22,rof:0.068,mag:71,res:213,reload:2.8,spread:0.07,range:17,speed:42,auto:true,len:0.55,snd:'smg'},
 mosin:{name:'Mosin-Nagant',cal:'7.62×54R',dmg:80,rof:1.3,mag:5,res:60,reload:3.2,spread:0.012,range:40,speed:60,auto:false,len:0.9,snd:'rifle'},
 svt:{name:'SVT-40',cal:'7.62×54R',dmg:55,rof:0.45,mag:10,res:60,reload:2.6,spread:0.022,range:34,speed:58,auto:false,len:0.85,snd:'rifle'},
 dp:{name:'DP-28',cal:'7.62×54R',dmg:36,rof:0.11,mag:47,res:188,reload:4.2,spread:0.05,range:34,speed:58,auto:true,len:0.9,snd:'lmg'},
 ptrd:{name:'PTRD-41',cal:'14.5×114 mm',dmg:120,rof:0.3,mag:1,res:30,reload:2.3,spread:0.012,range:44,speed:70,auto:false,len:1.2,snd:'ptrd',at:true},
 mp40:{name:'MP 40',cal:'9×19 mm',dmg:20,rof:0.11,mag:32,res:96,reload:2.5,spread:0.08,range:16,speed:40,auto:true,len:0.55,snd:'smg2'},
 kar98:{name:'Kar98k',cal:'7.92×57 mm',dmg:52,rof:1.6,mag:5,res:40,reload:3,spread:0.03,range:36,speed:60,auto:false,len:0.88,snd:'rifle2'},
 mg42:{name:'MG 42',cal:'7.92×57 mm',dmg:22,rof:0.05,mag:75,res:999,reload:4.5,spread:0.07,range:38,speed:60,auto:true,len:0.95,snd:'mg42'},
};
const SOV_CALS=['7.62×25 mm','7.62×54R','14.5×114 mm'];
const SQUAD=[
 {name:'Orlov',rank:'Jr. Lt.',col:'#45b5aa',wpn:'svt'},
 {name:'Ivanov',rank:'Sgt.',col:'#5a84d6',wpn:'ppsh'},
 {name:'Morozov',rank:'Cpl.',col:'#a774d6',wpn:'dp'},
 {name:'Petrova',rank:'Sniper',col:'#66b85e',wpn:'mosin'},
 {name:'Sokolova',rank:'Pvt.',col:'#e6843f',wpn:'mosin'},
 {name:'Kuznetsov',rank:'Pvt.',col:'#e3be3c',wpn:'ptrd'},
 {name:'Lebedev',rank:'Pvt.',col:'#e9e3d1',wpn:'ppsh'},
];
const WAVES=[
 {r:9,s:3,m:0,g:2,t:0,txt:'A probing attack in strength. Riflemen are pouring through the ruins.'},
 {r:10,s:7,m:1,g:3,t:0,txt:'Assault troops with MP 40s are coming in fast behind an MG 42.'},
 {r:12,s:9,m:2,g:3,t:0,txt:'Two MG 42 teams are setting up in no-man\'s land. Get them before they shred the windows.'},
 {r:13,s:10,m:2,g:4,t:1,txt:'A heavy assault on both flanks, with a Panzer in support. Watch the trenches.'},
 {r:15,s:12,m:2,g:4,t:1,txt:'Everything they have. A Panzer leads the last assault — only grenades and the PTRD can stop it.'},
];
// Avalon-style sorties between assaults. Team size per sortie (8 soldiers).
const SORTIES=[
 {name:'Wire the northern approach',x:31,y:7,brief:'Crawl out and lay wire and mines across the northern approach.',ok:'Wire and mines are down. The next assault will be thinner.',bad:'The mines were wired to fail. The next assault walks straight through.'},
 {name:'Raid the listening post',x:28,y:33,brief:'Clear the German listening post in the southern rubble before it calls in the next attack.',ok:'The listening post is gone. The Germans will come in blind and fewer.',bad:'The post survived and called in reinforcements.'},
 {name:'Cut the field telephone',x:25,y:20,brief:'Cut the German field telephone cable that runs under the street.',ok:'The line is cut. The next assault is badly coordinated.',bad:'The cable was never cut. The Germans mass more troops.'},
 {name:'Blow the culvert',x:23,y:12,brief:'Blow the culvert the Germans use to bring troops up under cover.',ok:'The culvert is rubble. Fewer Germans reach the line.',bad:'The charge was a dud. Germans pour through the culvert.'},
 {name:'Mine the street',x:30,y:21,tank:true,brief:'Mine the street before the Panzer comes. Last chance.',ok:'Mines in the street. The Panzer will hit them, and fewer Germans follow.',bad:'The mines were disarmed. The Panzer and its infantry come on in full strength.'},
];
const TEAM=[3,4,4,5,5];
// mul: German numbers per assault · spread: German inaccuracy · pdmg: German damage to you · hp: squad toughness
const DIFF={easy:{mul:0.6,spread:2.7,pdmg:0.6,hp:150,name:'Easy'},normal:{mul:1,spread:2.1,pdmg:0.8,hp:130,name:'Normal'},hard:{mul:1.3,spread:1.75,pdmg:1,hp:115,name:'Hard'}};
let UID=0;
function mkUnit(o){return Object.assign({id:UID++,alive:true,x:0,y:0,aim:Math.PI,hp:100,maxhp:100,path:[],moving:false,phase:0,fireCd:0,reloadT:0,burst:4,burstPause:0,thinkT:rnd()*0.3,target:null,state:'idle',timer:0,bark:null,grenCd:8+rnd()*12,side:'sov',uniform:'sov',isSpy:false,revealed:false,arrested:false,sight:{},plog:[],logT:0,sightT:rnd()*0.4,repathT:0,mag:0,kind:'sq',moveA:0},o)}

// ================= state =================
let G=null,state='boot',TS=36,VW=0,VH=0,DPR=1,camX=0,camY=0;
const cv=$('cv'),ctx=cv.getContext('2d');const fog=document.createElement('canvas'),fctx=fog.getContext('2d');
const KEYS={},MOUSE={x:0,y:0,down:false,in:false},TCH={mx:0,my:0,ax:0,ay:0,aiming:false,fire:false};
const VIS=17;
const inDugout=u=>u.x>=54&&u.x<=58&&u.y>=16&&u.y<=24;

const SEATS=8;
const HCOL=['#ef5a3c','#4fc3f7','#f06292','#c6e57a','#ffb74d','#b388ff','#4db6ac','#fff176'];
// which AI soldiers stay when humans take seats (the PTRD gunner is kept longest — the line needs him for the Panzer)
const BOT_KEEP=['Kuznetsov','Orlov','Petrova','Morozov','Sokolova','Ivanov','Lebedev'];
// cfg: {seed, diff, humans:[{name}], rolePref?(single player: 'comrade'|'regular'|'spy'|'random'), demo?}
function newGame(cfg){
  UID=0;RS=(cfg.seed|0)||1;resetMap();
  const DF=DIFF[cfg.diff]||DIFF.normal;
  G={diff:DF,diffKey:cfg.diff||'normal',comGuess:{},pub:{},rec:{},track:[],mi:0,mission:null,council:null,fails:0,comKnown:false,aiArrests:3,mod:null,units:[],proj:[],nades:[],fx:[],bodies:[],sched:[],incidents:[],log:[],smoke:[],phase:'lull',phaseT:22,wave:0,time:0,tick:0,spawnQ:[],spawnT:0,overrun:0,
    kills:0,lost:0,susp:{},hitInd:[],dmgFlash:0,shake:0,over:false,spyFate:null,incId:0,kick:0,arrestDone:false,banner:null,demo:!!cfg.demo};
  const hs=cfg.demo?[]:cfg.humans;
  G.humans=hs.map((h,i)=>{const p=mkUnit({kind:'player',isPlayer:true,seat:i,name:String(h.name||'Rybakov').trim().slice(0,12)||'Rybakov',rank:'Pvt.',col:HCOL[i%HCOL.length],wpn:'ppsh',mag:71,reserve:213,x:49.5-(i%4)*0.9,y:16.5+(i>>2)*0.9,aim:Math.PI,grenades:3,flares:0,slot:0,notes:[],arrestsLeft:2,crateCd:0,kills:0,away:false});
    p.slots=[{wpn:'ppsh',mag:71,reserve:213},null];G.units.push(p);return p});
  const nb=cfg.demo?SQUAD.length:Math.max(0,SEATS-hs.length);const keep=new Set(BOT_KEEP.slice(0,nb));
  const bots=SQUAD.filter(s=>keep.has(s.name));const posts=assignPostsList(bots.length);
  bots.forEach((s,i)=>{const u=mkUnit({kind:'sq',name:s.name,rank:s.rank,col:s.col,wpn:s.wpn,mag:WPN[s.wpn].mag,post:posts[i],hp:DF.hp,maxhp:DF.hp});u.x=u.post.x;u.y=u.post.y;u.aim=u.post.face;G.units.push(u)});
  G.squad=G.units.filter(u=>u.kind==='sq');G.people=[...G.humans,...G.squad];
  // secret roles: one spy, one commissar, the rest regulars
  let spy,com;const pref=G.humans.length===1?cfg.rolePref:null;let pr=pref==='random'?(()=>{const r=rnd();return r<1/8?'spy':r<2/8?'comrade':'regular'})():pref;
  if(pr==='spy')spy=G.humans[0];else spy=pick(pr?G.squad:G.people);
  if(pr==='comrade')com=G.humans[0];else com=pick((pr?G.squad:G.people).filter(u=>u!==spy));
  spy.isSpy=true;G.spy=spy;if(!spy.isPlayer){spy.stabCd=1e9;spy.flareCd=1e9;spy.flaresLeft=0}
  com.isCom=true;G.com=com;if(!com.isPlayer)com.qCd=8+rnd()*8;
  G.order=shuffle([...G.people]);G.lead=0;
  G.me=G.humans[0]||null}
// the grid is changed in play (a burnt-out Panzer becomes cover), so every game starts from a pristine copy
let GRID0=null,CK0=null;
function resetMap(){if(!GRID0){GRID0=grid.slice();CK0=ck.slice()}grid.set(GRID0);ck.set(CK0);FIRES.length=FIRES0;for(const s of CSPOTS)s.res=null}
const humans=()=>G.humans;
const liveHumans=()=>G.humans.filter(h=>h.alive);
function seesPt(h,x,y,r){return !!(h&&h.alive&&dist(h.x,h.y,x,y)<=(r||VIS)&&los(h.x,h.y,x,y))}
const roleOf=u=>u.isSpy?'spy':u.isCom?'com':'reg';
function assignPostsList(n){
  const by=c=>shuffle(POSTS.filter(p=>p.c===c));const win=by('win'),side=by('side'),ntr=by('ntr'),str=by('str'),dug=by('dug');
  return shuffle([win[0],win[1],win[4],ntr[0],str[0],dug[0],side[0],win[2]].slice(0,n))}
function assignPosts(){const live=G.squad.filter(u=>u.alive&&!u.revealed);const ps=assignPostsList(live.length);live.forEach((u,i)=>{u.post=ps[i];u.seeking=false})}
const liveSov=()=>G.units.filter(u=>u.alive&&u.side==='sov');
const liveSquad=()=>G.squad.filter(u=>u.alive&&u.side==='sov');
function getOfficer(ex){for(const n of ['Orlov','Ivanov','Morozov','Petrova','Sokolova','Kuznetsov','Lebedev']){const u=G.squad.find(s=>s.name===n);if(u&&u.alive&&u.side==='sov'&&u!==ex&&!u.isSpy)return u}return null}
// who runs the inquiry when the player is not the commissar: the hidden AI commissar, or the ranking officer once he is dead
// the human commissar runs his own inquiry; otherwise the hidden AI commissar does, or the ranking officer once he is dead
function investigator(){const c=G.com;if(c&&c.alive&&c.side==='sov')return c.isPlayer?null:c;return getOfficer()}
const offTag=o=>o.isCom?`Commissar ${o.name}`:o.name;
const roster=()=>G.people.filter(u=>u&&u.alive&&u.side==='sov');
function addGuess(u,v){G.comGuess[u.id]=clamp((G.comGuess[u.id]||0)+v,0,100)}

// ================= messaging =================
// Everything here is display only: each peer shows what is meant for its own player. None of it may touch rnd().
// `to`: undefined = everyone, a unit = only that player, a function = players it returns true for.
const forMe=to=>!!G&&!!G.me&&(to===undefined||to===null||(typeof to==='function'?to(G.me):to===G.me));
const LOYAL=h=>!h.isSpy;
function logMsg(t,k,to){if(!forMe(to))return;G.log.push({t,k:k||'',at:performance.now()});if(G.log.length>4)G.log.shift();renderRadio()}
function renderRadio(){$('radio').innerHTML=G.log.map(l=>`<div class="${l.k}">${esc(l.t)}</div>`).join('')}
function clock(){const s=G.time|0;return`${String(s/60|0).padStart(2,'0')}:${String(s%60).padStart(2,'0')}`}
// notes live on each human's unit, so they are the same on every peer and survive a rejoin
function noteTo(h,t,k){if(!h||!h.isPlayer)return;h.notes.push({t,k:k||'',when:`${G.wave?'Assault '+G.wave:'Before the attack'} · ${clock()}`});if(h===G.me)$('noteBtn').classList.add('flash')}
function noteAll(t,k,f){for(const h of G.humans)if(!f||f(h))noteTo(h,t,k)}
function say(u,t,d){u.bark={t,life:d||2.2}}
function banner(h,p,k,d,to){if(!forMe(to))return;G.banner={life:d||3.6};const b=$('banner');b.className=k||'';b.querySelector('h2').textContent=h;b.querySelector('p').textContent=p||'';b.hidden=false}
let speechTO=null;function speech(name,text,to){if(!forMe(to))return;const s=$('speech');s.innerHTML=`<b>${esc(name)}</b>${esc(text)}`;s.hidden=false;clearTimeout(speechTO);speechTO=setTimeout(()=>s.hidden=true,8000)}

// ================= combat core =================
function fire(u,ang,o={}){
  if(u.fireCd>0||u.reloadT>0)return false;
  if(u.mag<=0){startReload(u);return false}
  const w=WPN[u.wpn];
  let sp=w.spread*(u.isPlayer?1:(u.side==='ger'?G.diff.spread:1.5))*(o.extra||1);
  if(u.isPlayer&&u.moving)sp*=1.6;
  const a=ang+(rnd()+rnd()-1)*sp*1.5,dx=Math.cos(a),dy=Math.sin(a);
  const tk=!!o.tk||(u.isPlayer&&u.isSpy&&!u.revealed);
  G.proj.push({x:u.x+dx*0.3,y:u.y+dy*0.3,dx,dy,sp:w.speed,dmg:w.dmg*(o.mul||1),cal:w.cal,owner:u,side:u.side,tk,dist:0,max:w.range*1.3,at:!!w.at,last:-1,he:false});
  u.mag--;u.fireCd=w.rof*(u.isPlayer?1:1+rnd()*0.25);
  const ml=w.len+0.1;G.fx.push({k:'muz',x:u.x+dx*ml,y:u.y+dy*ml,a,t:0,life:0.06});
  sfxAt(w.snd,u.x,u.y);
  if(u===G.me)G.kick=Math.min(0.25,G.kick+0.06);
  if(u.mag<=0)startReload(u);
  return true}
function startReload(u){if(u.reloadT>0)return;const w=WPN[u.wpn];if(u.isPlayer&&(u.reserve<=0||u.mag>=w.mag))return;u.reloadT=w.reload;if(u.isPlayer){if(u===G.me)sfx('reload')}else if(w.mag>5&&rnd()<0.5)say(u,pick(['Reloading!','Changing drum!','Cover me!']),1.4)}
function canHit(p,u){if(u===p.owner||!u.alive)return false;if(u.kind==='tank')return p.side!=='ger';const s=p.side,t=u.side;
  if(s==='ger')return t==='sov';if(s==='sov')return t==='ger'||t==='traitor'||(t==='sov'&&p.tk);if(s==='traitor')return t==='sov';return false}
function updateProj(dt){
  for(const p of G.proj){let rem=p.sp*dt;
    while(rem>0&&!p.dead){const st=Math.min(0.3,rem);rem-=st;const nx=p.x+p.dx*st,ny=p.y+p.dy*st;
      let best=null,bt=2;
      for(const u of G.units){if(!canHit(p,u))continue;const r=u.kind==='tank'?1.15:0.36;const fx=u.x-p.x,fy=u.y-p.y;const t=clamp((fx*p.dx+fy*p.dy)/st,0,1);const cx=p.x+p.dx*st*t,cy=p.y+p.dy*st*t;if(dist(cx,cy,u.x,u.y)<r&&t<bt){bt=t;best=u}}
      if(best){const hx=p.x+p.dx*st*bt,hy=p.y+p.dy*st*bt;p.dead=true;
        if(best.kind==='tank'){if(p.at){hurt(best,90,{owner:p.owner,cause:'bullet',cal:p.cal,dx:p.dx,dy:p.dy});G.fx.push({k:'spark',x:hx,y:hy,t:0,life:0.3,n:8})}else{G.fx.push({k:'spark',x:hx,y:hy,t:0,life:0.15,n:3});if(crnd()<0.3)sfxAt('ric',hx,hy)}}
        else if(p.he)explode(hx,hy,2.2,95,{owner:p.owner,cause:'shell',hurtSov:true,hurtGer:false});
        else hurt(best,p.dmg,{owner:p.owner,cause:'bullet',cal:p.cal,dx:p.dx,dy:p.dy,tk:p.tk,at:p.at});
        break}
      p.x=nx;p.y=ny;p.dist+=st;
      if(nx<0||ny<0||nx>=W||ny>=H){p.dead=true;break}
      const ti=(ny|0)*W+(nx|0),t=grid[ti];
      if(t===WALL){p.dead=true;if(p.he)explode(nx-p.dx*0.3,ny-p.dy*0.3,2.2,95,{owner:p.owner,cause:'shell',hurtSov:true,hurtGer:false});else impact(nx-p.dx*0.15,ny-p.dy*0.15);break}
      if((t===COVER||t===WIN||t===CRATE)&&p.dist>1.4&&p.last!==ti){p.last=ti;if(!p.he&&rnd()<(t===WIN?0.6:0.5)){p.dead=true;impact(nx,ny);break}}
      if(p.he&&p.dist>=p.max){p.dead=true;explode(nx,ny,2.2,95,{owner:p.owner,cause:'shell',hurtSov:true,hurtGer:false});break}
      if(p.dist>p.max){p.dead=true;break}}}
  G.proj=G.proj.filter(p=>!p.dead)}
function impact(x,y){if(!G.me||dist(x,y,G.me.x,G.me.y)>VIS+4)return;G.fx.push({k:'dust',x,y,t:0,life:0.45});if(crnd()<0.4)G.fx.push({k:'spark',x,y,t:0,life:0.12,n:2});if(crnd()<0.06)sfxAt('ric',x,y)}
function dirKey(s){if(s.cause!=='bullet'||s.dx===undefined)return'none';if(s.dx<-0.35)return'behind';if(s.dx>0.35)return'front';return'flank'}
function hurt(u,dmg,src){
  if(!u.alive)return;
  if(u.isPlayer&&src.owner&&src.owner.side==='ger')dmg*=G.diff.pdmg;
  if(u.isPlayer&&G.god)dmg=0;
  u.hp-=dmg;
  if(u.kind!=='tank'){G.fx.push({k:'blood',x:u.x,y:u.y,t:0,life:0.4});if(crnd()<0.5)decal('blood',u.x+(crnd()-.5)*.5,u.y+(crnd()-.5)*.5)}
  if(u.isPlayer){
    const friendly=!!(src.owner&&src.owner.side!=='ger'&&src.owner!==u);
    if(u===G.me){const a=src.dx!==undefined?Math.atan2(-src.dy,-src.dx):0;G.hitInd.push({a,t:0,life:1.2,friendly});G.dmgFlash=0.35;sfx('hurt')}
    if(!u.isSpy&&src.cause==='bullet'&&friendly&&!src.owner.revealed&&G.time-(u.ffNoteT||-99)>4){u.ffNoteT=G.time;
      noteTo(u,`You were shot ${dirKey(src)==='behind'?'in the back, from our own side of the line,':'from the '+dirKey(src)} with a ${src.cal} round at the ${zoneAt(u.x,u.y)}.`,'key');
      logMsg(`You were hit by a ${src.cal} round from our own side!`,'bad',u);
      if(src.owner.alive&&seesPt(u,src.owner.x,src.owner.y,10)){noteTo(u,`You spun round and saw ${src.owner.name} holding the gun.`,'key');
        if(src.tk&&src.owner.isSpy&&u.hp>0)reveal(src.owner,`shot ${u.name} in the back`,u)}}}
  else if(u.side==='sov'&&src.tk&&src.owner&&src.owner!==u){
    const s=src.owner;
    if(u.hp>0&&s.alive&&!s.revealed&&dist(u.x,u.y,s.x,s.y)<10&&los(u.x,u.y,s.x,s.y)){say(u,'Traitor!',2.5);reveal(s,`shot ${u.name}`,u)}
    else if(u.hp>0){say(u,'I\'m hit — from behind!',2.2);if(s.isPlayer&&s.isSpy)G.incidents.push({id:++G.incId,type:'hit',t:G.time,x:u.x,y:u.y,zone:zoneAt(u.x,u.y),cal:src.cal,victimName:u.name,wave:G.wave})}
    if(s.isPlayer&&s.isSpy&&!s.revealed&&src.cause==='bullet'){const w=noticedBy(s,u);if(w.length){say(w[0],'Traitor!',2.5);reveal(s,`shot ${u.name}`,w[0])}}}
  if(u.hp<=0)kill(u,src)}
function kill(u,src){
  u.alive=false;u.hp=0;u.path=[];if(u.res){u.res.res=null;u.res=null}
  for(const h of G.humans)if(h.arrestHold&&(h.arrestHold.T===u||h===u))h.arrestHold=null;
  const ko=src.owner&&src.owner.isPlayer?src.owner:null;
  if(u.kind==='tank'){u.dead=true;G.kills++;if(ko)ko.kills++;for(let dy=-1;dy<=1;dy++)for(let dx=-1;dx<=1;dx++){const tx=(u.x|0)+dx,ty=(u.y|0)+dy;if(get(tx,ty)===GROUND)set(tx,ty,COVER,5)}explode(u.x,u.y,2.5,60,{owner:u,cause:'shell',hurtSov:true,hurtGer:true});logMsg('The Panzer is burning!','good');FIRES.push({x:u.x,y:u.y,big:true});return}
  const b={u,x:u.x,y:u.y,aim:u.aim,uniform:u.uniform,col:u.col,cause:src.cause||'bullet',cal:src.cal,gkind:src.gkind,dirKey:dirKey(src),t:G.time,wave:G.wave,zone:zoneAt(u.x,u.y),inspected:false,inspBy:[],wpn:(u.side==='ger'&&(u.wpn==='mp40'||u.wpn==='kar98'))?u.wpn:null,taken:false,killer:src.owner};
  G.bodies.push(b);decal('pool',u.x,u.y);
  if(u.side==='ger'){G.kills++;if(ko)ko.kills++;return}
  if(u.isCom&&G.spy&&src.owner===G.spy){const sp=G.spy;
    endGame(true,me=>me.isSpy?`You killed ${u.name} — the commissar. Without him the inquiry dies, and nobody will ever know it was you.`:
      me===u?`${sp.name}, the spy, worked out you were the commissar and killed you at the ${b.zone}.`:`The spy found the commissar first. ${u.name} was killed at the ${b.zone}, and the inquiry died with him.`);return}
  if(u.isCom){G.comKnown=true;logMsg(`${u.name} is down — ${u.name} was the commissar.`,'bad');noteAll(`${u.name} was the secret commissar, and is dead. The ranking officer takes over the inquiry.`,'key',h=>h!==u)}
  if(u.isPlayer&&G.humans.length===1){
    if(u.isSpy)endGame(false,u.revealed?'Cut down by the comrades you betrayed, short of the German lines.':`You were killed at the ${b.zone}.`);
    else endGame(true,`You were killed at the ${b.zone}${src.owner&&src.owner.side!=='ger'?` — by ${src.owner.name}`:''}.`);return}
  if(u.isPlayer)banner('You were killed',`At the ${b.zone}. You can watch the rest of the battle.`,'bad',5,u);
  if(u.side==='traitor'){G.spyFate='killed';logMsg(`${u.name}, the spy, is dead.`,'good');noteAll(`${u.name} — the spy — was killed before reaching the German lines.`,'key',LOYAL);banner('Spy eliminated',`${u.name} will not reach the Germans.`,'good',3.6,LOYAL);allHumansDown();return}
  G.lost++;
  const inc={id:++G.incId,type:'death',t:G.time,x:u.x,y:u.y,zone:b.zone,victim:u,victimName:u.name,body:b,wave:G.wave};G.incidents.push(inc);b.inc=inc;
  logMsg(`${u.name} is down — ${b.zone}.`,'bad');
  noteAll(`${u.name} was killed at the ${b.zone}. Find the body and inspect it.`,'death',h=>!h.isSpy&&h!==u);
  if(u.isPlayer)allHumansDown()}
// in a multiplayer room the battle goes on while any player is alive
function allHumansDown(){if(G.humans.length&&!G.humans.some(h=>h.alive))endGame(!G.spy.isPlayer,'Every player in the squad has fallen. The bots cannot hold the block alone.')}
function explode(x,y,r,dmg,o){
  G.fx.push({k:'boom',x,y,t:0,life:0.5,r});for(let i=0;i<5;i++)G.smoke.push({x:x+(crnd()-.5),y:y+(crnd()-.5),r:0.6+crnd()*0.6,t:0,life:3+crnd()*3,vx:0.3+crnd()*0.3,vy:-0.2+crnd()*0.2,dark:true});
  decal('crater',x,y,r);sfxAt(o.cause==='shell'||o.cause==='mortar'?'boomBig':'boom',x,y);
  if(G.me){const d=dist(x,y,G.me.x,G.me.y);G.shake=Math.max(G.shake,(REDUCED?3:14)*clamp(1-d/18,0,1))}
  for(const u of G.units){if(!u.alive)continue;const d=dist(x,y,u.x,u.y);const rr=u.kind==='tank'?r+1.1:r;if(d>rr)continue;if(!los(x,y,u.x,u.y,0.3))continue;
    if(u.kind==='tank'){if(o.cause==='grenade'||o.cause==='mortar')hurt(u,190*(1-d/rr)+30,{owner:o.owner,cause:o.cause});continue}
    if(u.side==='sov'&&!o.hurtSov)continue;if(u.side==='ger'&&!o.hurtGer)continue;if(u.side==='traitor'&&!o.hurtGer)continue;
    hurt(u,dmg*(1-d/rr*0.75),{owner:o.owner,cause:o.cause,gkind:o.gkind,dx:(u.x-x)/(d||1),dy:(u.y-y)/(d||1),tk:o.tk})}}
function throwGrenade(u,tx,ty,kind){
  const d=Math.min(dist(u.x,u.y,tx,ty),11),a=Math.atan2(ty-u.y,tx-u.x);
  let ex=u.x+Math.cos(a)*d,ey=u.y+Math.sin(a)*d;const n=Math.ceil(d/0.2);for(let i=1;i<=n;i++){const x=u.x+Math.cos(a)*d*i/n,y=u.y+Math.sin(a)*d*i/n;if(get(x|0,y|0)===WALL){ex=u.x+Math.cos(a)*d*Math.max(0,i-1.5)/n;ey=u.y+Math.sin(a)*d*Math.max(0,i-1.5)/n;break}}
  const sov=u.side==='sov';
  G.nades.push({x:u.x,y:u.y,sx:u.x,sy:u.y,tx:ex,ty:ey,t:0,T:0.7+d*0.05,fuse:kind==='stick'?3:2.7,owner:u,kind,z:0,
    o:{owner:u,cause:'grenade',gkind:kind,hurtSov:!sov||(u.isPlayer&&u.isSpy),hurtGer:true,tk:u.isPlayer&&u.isSpy&&!u.revealed}});
  sfxAt('throw',u.x,u.y)}
function updateNades(dt){for(const n of G.nades){n.t+=dt;n.fuse-=dt;const k=Math.min(1,n.t/n.T);n.x=n.sx+(n.tx-n.sx)*k;n.y=n.sy+(n.ty-n.sy)*k;n.z=4*k*(1-k);
    if(n.fuse<=0){n.dead=true;explode(n.x,n.y,2.8,115,n.o)}}G.nades=G.nades.filter(n=>!n.dead)}

// ================= sight / noticing =================
function noticedBy(s,ex){const out=[];for(const o of G.units){if(!o.alive||o===s||o===ex||o.side!=='sov'||o.isSpy||(o.kind!=='sq'&&!o.isPlayer))continue;
  if(o.isPlayer){if(seesPt(o,s.x,s.y,10))out.push(o);continue}
  const d=dist(o.x,o.y,s.x,s.y);if(d>12)continue;if(!los(o.x,o.y,s.x,s.y,0.35))continue;
  const cone=o.target&&o.target.alive?0.6:0.95;
  if(d<2.5||Math.abs(angDiff(o.aim,Math.atan2(s.y-o.y,s.x-o.x)))<cone)out.push(o)}return out}
function pickTarget(u){
  const w=WPN[u.wpn];let best=null,bs=1e9;const range=u.kind==='tank'?40:w.range;
  for(const e of G.units){if(!e.alive||e===u)continue;
    let foe=false;if(u.side==='sov')foe=e.side==='ger'||e.side==='traitor';else if(u.side==='ger')foe=e.side==='sov';else if(u.side==='traitor')foe=e.side==='sov';
    if(!foe)continue;const d=dist(u.x,u.y,e.x,e.y);if(d>range)continue;
    let s=d;if(u.wpn==='ptrd'&&e.kind==='tank')s-=40;if(u.wpn==='mosin'&&e.kind==='mg')s-=12;if(e.side==='traitor')s-=15;if(e.kind==='tank'&&u.wpn!=='ptrd')s+=25;
    if(s>=bs)continue;if(!los(u.x,u.y,e.x,e.y,0.35))continue;bs=s;best=e}
  return best}

// ================= Soviet AI =================
function sovAI(u,dt){
  if(u.revealed){traitorAI(u,dt);return}
  if(u.isSpy)spyAI(u,dt);
  if(u.isCom)comAI(u,dt);
  if(u.stab){stabTick(u,dt);return}
  const ah=G.humans.find(h=>h.arrestHold&&h.arrestHold.T===u);if(ah){u.moving=false;u.path=[];u.aim=Math.atan2(ah.y-u.y,ah.x-u.x);return}
  if(u.path.length)followPath(u,dt,3.3);else u.moving=false;
  const M=G.mission;
  if(u.evadeT>0)u.evadeT-=dt;
  else if(u.sortie&&M&&M.st==='go'){if(!u.path.length&&!u.seeking&&dist(u.x,u.y,u.spot.x,u.spot.y)>0.6){u.repathT-=dt;if(u.repathT<=0){u.repathT=1;goTo(u,u.spot.x,u.spot.y)}}}
  else if(!u.path.length&&!u.seeking&&u.post&&dist(u.x,u.y,u.post.x,u.post.y)>0.35){u.repathT-=dt;if(u.repathT<=0){u.repathT=1.2;goTo(u,u.post.x,u.post.y)}}
  if(u.seeking&&!u.path.length){u.seekHold-=dt;if(u.seekHold<=0)u.seeking=false}
  combatTick(u,dt)}
function combatTick(u,dt){
  u.thinkT-=dt;if(u.thinkT<=0){u.thinkT=0.28+rnd()*0.12;u.target=pickTarget(u)}
  const t=u.target&&u.target.alive?u.target:null;
  const want=t?Math.atan2(t.y-u.y,t.x-u.x):(u.moving?u.moveA:(u.post?u.post.face:Math.PI));
  const d=angDiff(u.aim,want);u.aim+=clamp(d,-8*dt,8*dt);
  if(!t)return;
  if(Math.abs(d)<0.15){if(u.burstPause>0)u.burstPause-=dt;
    else{const w=WPN[u.wpn];const ex=(u.isSpy&&t.side==='ger')?2.8:1;
      if(fire(u,u.aim,{extra:ex})&&w.auto){u.burst--;if(u.burst<=0){u.burst=3+(rnd()*6|0);u.burstPause=0.3+rnd()*0.7}}}}
  u.grenCd-=dt;
  if(u.grenCd<=0&&t.side==='ger'&&G.phase==='wave'){const dd=dist(u.x,u.y,t.x,t.y);if(dd>4&&dd<11&&rnd()<0.6){throwGrenade(u,t.x,t.y,'rgd');say(u,pick(['Granata!','Grenade out!']),1.4);u.grenCd=16+rnd()*14}else u.grenCd=2}}
function traitorAI(u,dt){
  if(!u.fleeSet){u.fleeSet=true;u.post=null;if(!goTo(u,0.6,clamp(u.y,2,37)|0))goTo(u,0.6,20.5)}
  if(u.path.length)followPath(u,dt,3.7);else{u.repathT-=dt;if(u.repathT<=0){u.repathT=2;goTo(u,0.6,clamp(u.y+(rnd()-.5)*10,1,38)|0)}}
  if(u.x<1.2){u.alive=false;u.escaped=true;G.spyFate='escaped';logMsg(`${u.name} reached the German lines.`,'bad');noteAll(`${u.name}, the spy, escaped to the Germans.`,'key',LOYAL);return}
  combatTick(u,dt)}
// the AI spy's best guess at who the hidden commissar is (only acts on a strong guess)
function comTarget(u){let best=null,bv=0;for(const o of liveSov()){if(o===u)continue;const v=G.comGuess[o.id]||0;if(v>bv){bv=v;best=o}}return bv>=55?best:null}
function spyAI(u,dt){
  if(u.revealed)return;
  const M=G.mission,onSortie=u.sortie&&M&&M.st==='go';
  if(!(G.phase==='wave'&&G.wave>=2)&&!onSortie)return;
  u.stabCd-=dt;u.flareCd-=dt;u.spyT=(u.spyT||0)-dt;u.seekT=(u.seekT||0)-dt;
  if(u.spyT>0||u.stab)return;u.spyT=0.35;
  if(!onSortie&&u.flaresLeft>0&&u.flareCd<=0){if(noticedBy(u,null).length===0){doFlare(u);u.flaresLeft--}else u.flareCd=2;return}
  if(u.stabCd<=0){
    const C=comTarget(u);
    if(C){const d=dist(u.x,u.y,C.x,C.y);if(d<9&&d>1&&los(u.x,u.y,C.x,C.y)&&noticedBy(u,C).length===0){startStab(u,C);return}
      if(u.seekT<=0){u.seekT=5+rnd()*3;const sp=behindSpot(C);if(sp&&goTo(u,sp.x,sp.y)){u.seeking=true;u.seekHold=6}}return}
    if(onSortie)return;
    const cands=G.units.filter(o=>o.alive&&o.side==='sov'&&!o.isSpy&&o!==u&&(o.kind==='sq'||(o.isPlayer&&o.hp>=70&&rnd()<0.3)));
    for(const T of shuffle(cands)){const d=dist(u.x,u.y,T.x,T.y);if(d<9&&d>1&&los(u.x,u.y,T.x,T.y)&&noticedBy(u,T).length===0){startStab(u,T);return}}
    if(u.seekT<=0){u.seekT=8+rnd()*5;const T=lonelyTarget(u);if(T){const sp=behindSpot(T);if(sp&&goTo(u,sp.x,sp.y)){u.seeking=true;u.seekHold=7}}}}}
function comAI(u,dt){
  const M=G.mission;
  if(G.phase!=='lull'||u.sortie||u.stab||G.council){if(u.q){u.q=null;u.seeking=false}return}
  u.qCd=(u.qCd===undefined?8:u.qCd)-dt;
  if(u.q){const T=u.q.T;u.q.time-=dt;
    if(!T.alive||T.side!=='sov'||u.q.time<=0){u.q=null;u.seeking=false;u.qCd=10+rnd()*10;return}
    if(dist(u.x,u.y,T.x,T.y)>1.8){u.q.rp-=dt;if(u.q.rp<=0){u.q.rp=1;goTo(u,T.x+(T.x<50?0.8:-0.8),T.y)}return}
    u.path=[];u.aim=Math.atan2(T.y-u.y,T.x-u.x);
    if(!u.q.talk){u.q.talk=2.6;say(u,pick([`A word, ${T.name}.`,`${T.name}. Where were you?`,'Show me your weapon, comrade.']),2.4);if(!T.isPlayer){say(T,pick(['Comrade?','I was at my post!','Yes, comrade.']),2.2);T.aim=Math.atan2(u.y-T.y,u.x-T.x)}comSeen(u,T)}
    u.q.talk-=dt;if(u.q.talk<=0){u.q=null;u.seeking=false;u.qCd=14+rnd()*12}return}
  if(u.qCd<=0){const c=roster().filter(o=>o!==u&&!o.sortie);if(c.length){u.q={T:pick(c),rp:0,time:16,talk:0};u.seeking=true;u.seekHold=99}else u.qCd=5}}
// someone saw the AI commissar questioning T
function comSeen(c,T){
  const sp=G.spy;
  if(sp&&sp.alive&&!sp.revealed&&!sp.isPlayer){const seen=dist(sp.x,sp.y,c.x,c.y)<13&&los(sp.x,sp.y,c.x,c.y,0.35);addGuess(c,(seen?35:10)+(T===sp?40:0))}
  const line=T.isPlayer?pick(['Where were you when the last comrade fell? Think carefully.','Your rifle. When did you last clean it? Show me.','I am watching everyone, comrade. Including you.']):'';
  for(const h of G.humans){if(!h.alive)continue;
    if(T===h){speech(`${c.rank} ${c.name}`,line,h);noteTo(h,`${c.name} took you aside and questioned you. ${h.isSpy?'Only the commissar does that.':`So the commissar is ${c.name}. Keep that to yourself.`}`,'key')}
    else if(seesPt(h,c.x,c.y,14))noteTo(h,`You saw ${c.name} quietly questioning ${T.name}.${h.isSpy?' Only the commissar asks questions.':''}`,'talk')}}
function lonelyTarget(u){let best=null,bs=1e9;for(const T of G.squad){if(!T.alive||T===u||T.side!=='sov')continue;let c=0;for(const o of liveSov())if(o!==T&&o!==u&&dist(o.x,o.y,T.x,T.y)<7)c++;const s=c*10+dist(u.x,u.y,T.x,T.y)*0.3+rnd()*4;if(s<bs){bs=s;best=T}}return best}
function behindSpot(T){for(let k=0;k<20;k++){const x=T.x+2+rnd()*3,y=T.y+(rnd()-.5)*5;if(passable(x|0,y|0)&&los(x,y,T.x,T.y))return{x:(x|0)+0.5,y:(y|0)+0.5}}return null}
function startStab(u,T){
  const sw=(u.wpn==='ptrd'||(G.wave>=3&&rnd()<0.3))?'mp40':u.wpn;
  G.stabs=(G.stabs||0)+1;u.stab={T,shots:WPN[sw].auto?4:2,t:0,prevW:u.wpn};u.wpn=sw;u.mag=WPN[sw].mag;u.reloadT=0;u.fireCd=0;u.path=[];
  for(const h of G.humans)if(h!==u&&seesPt(h,u.x,u.y,10)){noteTo(h,`You saw ${u.name} turn ${sw==='mp40'?'a German MP 40':'a weapon'} on ${T===h?'you':T.name}!`,'key');logMsg(`${u.name} is firing at ${T===h?'you':T.name}!`,'bad',h)}}
function stabTick(u,dt){const s=u.stab,T=s.T;u.moving=false;
  u.aim=Math.atan2(T.y-u.y,T.x-u.x);s.t-=dt;
  if(s.shots>0&&s.t<=0&&T.alive){u.fireCd=0;u.reloadT=0;if(u.mag<=0)u.mag=WPN[u.wpn].mag;fire(u,u.aim,{tk:true,mul:T.isPlayer?1.0:2.4,extra:0.35});s.shots--;s.t=WPN[u.wpn].auto?0.09:0.6}
  if(!u.stab)return;
  if((s.shots<=0&&s.t<=0)||!T.alive){u.wpn=s.prevW;u.mag=WPN[u.wpn].mag;u.stab=null;u.stabCd=40+rnd()*25;u.seeking=false;u.repathT=0.5}}
function doFlare(u,tx,ty){
  const C=tx===undefined&&!u.isPlayer?comTarget(u):null;if(C){tx=C.x;ty=C.y}
  if(tx===undefined){let best=null,bc=-1;for(const a of liveSov()){if(a===u)continue;let c=0;for(const b of liveSov())if(dist(a.x,a.y,b.x,b.y)<5)c++;if(c>bc){bc=c;best=a}}if(!best)return;tx=best.x;ty=best.y}
  G.fx.push({k:'flare',x0:u.x,y0:u.y,x:tx,y:ty,t:0,life:9});sfxAt('flare',u.x,u.y);
  G.sched.push({at:G.time+7,k:'barrage',x:tx,y:ty,by:u});
  G.incidents.push({id:++G.incId,type:'flare',t:G.time,x:u.x,y:u.y,zone:zoneAt(u.x,u.y),by:u,wave:G.wave});
  logMsg('Green flare! German mortars will be on it — get clear!','bad');
  for(const b of G.squad){if(b.alive&&b.side==='sov'&&dist(b.x,b.y,tx,ty)<6){const a=rnd()*TAU;for(let k=0;k<12;k++){const x=b.x+Math.cos(a+k)*6,y=b.y+Math.sin(a+k)*6;if(passable(x|0,y|0)&&dist(x,y,tx,ty)>6){goTo(b,(x|0)+0.5,(y|0)+0.5);b.evadeT=12;break}}}}
  for(const h of G.humans){if(h.isSpy||h===u)continue;let t=`A green flare went up from the ${zoneAt(u.x,u.y)} — a signal to the German mortars.`;if(seesPt(h,u.x,u.y,12))t+=` You saw ${u.name} fire it.`;noteTo(h,t,'flare')}}
function barrage(tx,ty,by){for(let i=0;i<6;i++)G.sched.push({at:G.time+i*0.5,k:'shell',x:tx,y:ty,by})}
// scheduled events are plain data (not closures) so they can travel in a snapshot
function runSched(e){
  if(e.k==='barrage')barrage(e.x,e.y,e.by);
  else if(e.k==='shell'){const x=clamp(e.x+(rnd()-.5)*7,1,W-2),y=clamp(e.y+(rnd()-.5)*7,1,H-2);sfxAt('whistle',x,y);G.sched.push({at:G.time+1.0,k:'boom',x,y,by:e.by})}
  else if(e.k==='boom')explode(e.x,e.y,2.5,100,{owner:e.by,cause:'mortar',hurtSov:true,hurtGer:true});
  else if(e.k==='end')endGame(e.sw,ENDTXT[e.txt](e));
  else if(e.k==='arrestOut'){const h=e.u;h.arrested=true;h.alive=false;banner('Arrested',`${e.tag} has taken you to the rear. You can watch the rest of the battle.`,'bad',5,h);allHumansDown()}}

// ================= German AI =================
function spawnGerman(kind){
  if(kind==='tank'){const th=Math.round(800*(G.tankMul||1));const u=mkUnit({kind:'tank',side:'ger',uniform:'ger',name:'Panzer',hp:th,maxhp:800,wpn:'mg42',mag:75,x:-1.5,y:20,aim:0,turret:0,shellCd:5});G.units.push(u);logMsg(G.tankMul<1?'Tank! The Panzer hit our mines — it is damaged, but still coming!':'Tank! A Panzer is coming down the street!','bad');sfx('tankHorn');return}
  let y=0;for(let k=0;k<40;k++){y=1+(rnd()*38|0);if(passable(0,y)&&passable(1,y))break}
  const wpn=kind==='smg'?'mp40':kind==='mg'?'mg42':'kar98';
  const u=mkUnit({kind,side:'ger',uniform:'ger',name:'German',wpn,mag:WPN[wpn].mag,x:0.5,y:y+0.5,aim:0,hp:kind==='mg'?140:100,maxhp:kind==='mg'?140:100,grenCd:kind==='gren'?6:30+rnd()*30});
  G.units.push(u);
  if(kind==='mg'){const c=CSPOTS.filter(s=>!s.res&&s.x>14&&s.x<27);if(c.length){const s=pick(c);if(goTo(u,s.x,s.y)){s.res=u;u.res=s;u.state='mgmove';return}}}
  nextMove(u)}
function nextMove(u){
  if(u.res){u.res.res=null;u.res=null}
  if(u.x>=34){assault(u);return}
  const st=u.kind==='smg'?[3,10]:[2,8];
  const c=CSPOTS.filter(s=>!s.res&&s.x>u.x+st[0]&&s.x<u.x+st[1]&&Math.abs(s.y-u.y)<7);
  if(!c.length){if(rnd()<0.5||u.x>28)assault(u);else{u.state='engage';u.timer=2+rnd()*2}return}
  const s=pick(c);if(goTo(u,s.x,s.y)){s.res=u;u.res=s;u.state='advance'}else{u.state='engage';u.timer=1.5}}
function assault(u){u.state='assault';const t=pick(ASSAULT);u.apt=t;if(!goTo(u,t.x,t.y)){u.state='engage';u.timer=2}u.repathT=3}
function gerAI(u,dt){
  u.thinkT-=dt;if(u.thinkT<=0){u.thinkT=0.3+rnd()*0.15;u.target=pickTarget(u)}
  const t=u.target&&u.target.alive?u.target:null;const sp=u.kind==='smg'?3.3:2.9;
  switch(u.state){
    case 'advance':if(u.path.length)followPath(u,dt,sp);else{u.moving=false;u.state='engage';u.timer=u.kind==='smg'?1+rnd()*2:2.5+rnd()*3.5}break;
    case 'engage':u.moving=false;u.timer-=dt;if(u.timer<=0)nextMove(u);break;
    case 'mgmove':if(u.path.length)followPath(u,dt,2.5);else{u.moving=false;u.state='mg';say(u,'MG — Feuer!',1.6)}break;
    case 'mg':u.moving=false;break;
    case 'hold':u.moving=false;break;
    case 'assault':if(u.path.length)followPath(u,dt,sp);else{u.moving=false;u.repathT-=dt;if(u.repathT<=0){u.repathT=2.5;if(!t&&dist(u.x,u.y,u.apt.x,u.apt.y)<2){u.apt=rnd()<0.6?ASSAULT[0]:pick(ASSAULT)}const tg=t||u.apt;if(tg)goTo(u,tg.x+(rnd()-.5),tg.y+(rnd()-.5))}}break;
    default:nextMove(u)}
  const want=t?Math.atan2(t.y-u.y,t.x-u.x):(u.moving?u.moveA:0);const d=angDiff(u.aim,want);u.aim+=clamp(d,-6*dt,6*dt);
  if(!t)return;const dd=dist(u.x,u.y,t.x,t.y);
  const canFire=u.state==='engage'||u.state==='mg'||u.state==='hold'||u.state==='assault'||(u.kind==='smg'&&dd<11);
  if(canFire&&Math.abs(d)<0.2){if(u.burstPause>0)u.burstPause-=dt;else{const w=WPN[u.wpn];if(fire(u,u.aim)&&w.auto){u.burst--;if(u.burst<=0){u.burst=u.kind==='mg'?10+(rnd()*10|0):3+(rnd()*5|0);u.burstPause=u.kind==='mg'?0.8+rnd()*1.2:0.4+rnd()*0.6}}}}
  u.grenCd-=dt;if(u.grenCd<=0){if(dd>4&&dd<10){throwGrenade(u,t.x,t.y,'stick');say(u,'Granate!',1.3);u.grenCd=u.kind==='gren'?10+rnd()*8:40}else u.grenCd=2}}
function tankAI(u,dt){
  if(u.x<27.5){u.x+=0.85*dt;u.moving=true;u.phase+=dt*6}else u.moving=false;
  u.thinkT-=dt;if(u.thinkT<=0){u.thinkT=0.5;u.target=pickTarget(u)}
  const t=u.target&&u.target.alive?u.target:null;
  const want=t?Math.atan2(t.y-u.y,t.x-u.x):0;const d=angDiff(u.turret,want);u.turret+=clamp(d,-1.1*dt,1.1*dt);u.aim=u.turret;
  u.shellCd-=dt;if(t&&u.shellCd<=0&&Math.abs(d)<0.06){u.shellCd=4.5+rnd()*2;const a=u.turret+(rnd()-.5)*0.04;const dd=dist(u.x,u.y,t.x,t.y)+(rnd()-.5)*1.5;
    G.proj.push({x:u.x+Math.cos(a)*1.8,y:u.y+Math.sin(a)*1.8,dx:Math.cos(a),dy:Math.sin(a),sp:30,dmg:0,cal:'75 mm',owner:u,side:'ger',dist:0,max:dd-1.8,he:true,last:-1});
    G.fx.push({k:'muz',x:u.x+Math.cos(a)*2.1,y:u.y+Math.sin(a)*2.1,a,t:0,life:0.12,big:true});sfxAt('cannon',u.x,u.y);G.shake=Math.max(G.shake,REDUCED?2:6)}
  if(t&&Math.abs(d)<0.3&&dist(u.x,u.y,t.x,t.y)<26){if(u.burstPause>0)u.burstPause-=dt;else if(fire(u,u.turret)){u.burst--;if(u.burst<=0){u.burst=8+(rnd()*8|0);u.burstPause=1+rnd()*1.5}}}}

// ================= human players =================
// Each tick every human contributes one input record (the only thing peers send each other):
//   [mx*100, my*100, aim*1000, buttons, events?]  buttons: 1 fire · 2 hold F (arrest) · 4 hold X (sabotage)
//   events: ['r'] reload · ['e'] use · ['g',x*100,y*100] grenade · ['t'] question · ['f'] start arrest · ['q',x*100,y*100] flare
//           ['s',slot] weapon · ['v',0|1] vote · ['p',[unit ids]] propose a sortie team
function humanTick(p,I,dt){
  p.btn=I?I[3]|0:0;
  if(!p.alive)return;
  const mx=I?clamp(I[0]/100,-1,1):0,my=I?clamp(I[1]/100,-1,1):0;
  if(I)p.aim=I[2]/1000;
  const l=Math.hypot(mx,my);
  if(l>0.1){const s=(p.reloadT>0?3.3:4.0)*Math.min(1,l)/l;moveFree(p,mx*s*dt,my*s*dt);p.moving=true;p.phase+=dt*10;p.moveA=Math.atan2(my,mx)}else p.moving=false;
  const trig=!!(p.btn&1);
  if(trig){const w=WPN[p.wpn];if(w.auto||!p.semiLock){if(fire(p,p.aim))p.semiLock=true;else if(p.mag<=0&&p.reserve<=0&&!(p.clickT>0)){if(p===G.me)sfx('empty');p.clickT=0.4}}}
  if(p.clickT>0)p.clickT=Math.max(0,p.clickT-dt);
  if(!trig)p.semiLock=false;
  if(I&&I[4])for(const e of I[4])humanEvent(p,e);
  if(p.arrestHold){const a=p.arrestHold;if(!a.T.alive||a.T.side!=='sov'||dist(p.x,p.y,a.T.x,a.T.y)>2.2||!(p.btn&2))p.arrestHold=null;else{a.t+=dt;if(a.t>=1.4){p.arrestHold=null;completeArrest(p,a.T)}}}
  if(p.revealed&&p.x<1.4){
    if(G.humans.length===1){endGame('escaped','You made it across no-man\'s land into the German lines, but your cover is gone for good.');return}
    p.alive=false;p.escaped=true;G.spyFate='escaped';logMsg(`${p.name} reached the German lines.`,'bad');banner('Escaped','You made it to the German lines. You can watch the rest of the battle.','',5,p);allHumansDown()}
  if(p.crateCd>0)p.crateCd-=dt}
function humanEvent(p,e){
  if(!Array.isArray(e))return;const k=e[0];
  if(k==='v'){councilVote(p,!!e[1]);return}
  if(k==='p'){councilPick(p,Array.isArray(e[1])?e[1]:[]);return}
  if(!p.alive||G.council)return;
  switch(k){
    case 'r':startReload(p);break;
    case 'e':doInteract(p);break;
    case 'g':playerGrenade(p,(e[1]|0)/100,(e[2]|0)/100);break;
    case 't':doAsk(p);break;
    case 'f':doArrestStart(p);break;
    case 'q':playerFlare(p,(e[1]|0)/100,(e[2]|0)/100);break;
    case 's':switchSlot(p,e[1]);break}}
function nearestInteract(p){
  if(!p||!p.alive||p.revealed)return null;
  for(const c of CRATES)if(dist(p.x,p.y,c.x,c.y)<1.6)return{k:'crate',label:'Resupply ammunition and grenades'};
  let best=null,bd=1.4;
  for(const b of G.bodies){const d=dist(p.x,p.y,b.x,b.y);if(d>=bd)continue;
    if(b.uniform==='sov'&&!b.inspBy.includes(p.id)&&!p.isSpy&&b.u!==p){best={k:'inspect',b,label:`Inspect ${b.u.name}'s body`};bd=d}
    else if(b.wpn&&!b.taken){best={k:'take',b,label:`Take the ${WPN[b.wpn].name} (${WPN[b.wpn].cal})`};bd=d}}
  return best}
// AI soldiers you can question
function nearestComrade(p,r){let best=null,bd=r;for(const u of G.squad){if(!u.alive||u.side!=='sov')continue;const d=dist(p.x,p.y,u.x,u.y);if(d<bd){bd=d;best=u}}return best}
// anyone the commissar can arrest, other players included
function nearestArrestable(p,r){let best=null,bd=r;for(const u of G.people){if(u===p||!u.alive||u.side!=='sov')continue;const d=dist(p.x,p.y,u.x,u.y);if(d<bd){bd=d;best=u}}return best}
function doInteract(p){
  const it=nearestInteract(p);if(!it)return;
  if(it.k==='crate'){if(p.crateCd>0)return;p.crateCd=1;storeSlot(p);p.slots[0].reserve=Math.max(p.slots[0].reserve,213);if(p.slots[1])p.slots[1].reserve=Math.max(p.slots[1].reserve,WPN[p.slots[1].wpn].res);p.reserve=p.slots[p.slot].reserve;p.grenades=3;if(p===G.me)sfx('reload');logMsg('Resupplied: full drums and three RGD-33 grenades.','good',p)}
  else if(it.k==='inspect'){it.b.inspBy.push(p.id);it.b.inspected=true;const t=inspectText(it.b);noteTo(p,t,'death');speech('You inspect the body',t,p);if(p===G.me)sfx('page');if(spySees(p))addGuess(p,8)}
  else if(it.k==='take'){it.b.taken=true;storeSlot(p);p.slots[1]={wpn:it.b.wpn,mag:WPN[it.b.wpn].mag,reserve:WPN[it.b.wpn].res};p.slot=1;loadSlot(p);if(p===G.me)sfx('reload');logMsg(`You picked up a German ${WPN[p.wpn].name}. Press 1 or 2 to switch.`,'',p)}}
function storeSlot(p){const s=p.slots[p.slot];if(s){s.mag=p.mag;s.reserve=p.reserve}}
function loadSlot(p){const s=p.slots[p.slot];p.wpn=s.wpn;p.mag=s.mag;p.reserve=s.reserve;p.reloadT=0;p.fireCd=0.25}
function switchSlot(p,i){if(i===-1||i===undefined)i=p.slot?0:1;if(!p.slots[i]||i===p.slot)return;storeSlot(p);p.slot=i;loadSlot(p);if(p===G.me)sfx('reload')}
function inspectText(b){const n=b.u.name;
  if(b.cause==='bullet'){const d={behind:'The round came from behind — from our side of the line.',front:'Shot from the front, from the German side.',flank:'Shot from the flank.',none:''}[b.dirKey];
    const ger=!SOV_CALS.includes(b.cal);return `${n}: a ${b.cal} round. ${d}${ger&&b.dirKey!=='front'?' A German calibre, but fired from inside our own lines.':''}`}
  if(b.cause==='grenade')return `${n}: grenade fragments, ${b.gkind==='rgd'?'from one of our own RGD-33s.':'from a German stick grenade.'}`;
  if(b.cause==='mortar')return `${n}: mortar shrapnel.`;
  if(b.cause==='shell')return `${n}: killed by a tank shell.`;return `${n}: cause unclear.`}
function doAsk(p){
  if(p.isSpy)return;const u=nearestComrade(p,2.6);if(!u)return;
  const inc=[...G.incidents].reverse().find(i=>i.type==='death'||i.type==='flare');
  u.aim=Math.atan2(p.y-u.y,p.x-u.x);
  if(!inc){const line=pick(['Nothing to report, comrade. Only Germans.','All quiet on my side, comrade.']);speech(`${u.rank} ${u.name}`,line,p);return}
  if(!u.answers)u.answers={};const key=inc.id+':'+p.id;let a=u.answers[key];const first=!a;
  if(!a)a=u.answers[key]=testimony(u,inc,p);
  const lab=inc.type==='death'?`${inc.victimName}'s death`:'the green flare';
  speech(`${u.rank} ${u.name} — about ${lab}`,a,p);
  if(first)noteTo(p,`${u.name}, about ${lab} (${inc.zone}): “${a}”`,'talk');if(p===G.me)sfx('page');
  // the spy can't tell a curious private from the commissar: anyone asking questions in his sight looks like the commissar
  if(first)addGuess(p,6+(spySees(p)?18:0)+(u.isSpy?30:0))}
// does the undercover AI spy have eyes on x?
function spySees(x){const s=G.spy;return !!(s&&s.alive&&!s.isPlayer&&!s.revealed&&dist(s.x,s.y,x.x,x.y)<13&&los(s.x,s.y,x.x,x.y,0.35))}
function posAt(u,t){let best=null,bd=1e9;for(const e of u.plog){const d=Math.abs(e.t-t);if(d<bd){bd=d;best=e}}return best||{x:u.x,y:u.y}}
function testimony(u,inc,asker){
  const p=posAt(u,inc.t);let my=zoneAt(p.x,p.y);const L=[];
  if(u.isSpy){if(dist(p.x,p.y,inc.x,inc.y)<11)my=pick(SOV_ZONES.filter(z=>z!==inc.zone&&z!==my));
    L.push(pick([`I was at the ${my}.`,`I was holding the ${my} the whole time.`]));
    const others=G.people.filter(x=>x!==u&&x!==asker&&x.alive&&x!==inc.victim);
    if(others.length&&rnd()<0.6)L.push(`I think I saw ${pick(others).name} moving toward the ${inc.zone} just before.`);else L.push('I didn\'t see anything — I was busy with the Fritzes.');return L.join(' ')}
  L.push(pick([`I was at the ${my}.`,`I was holding the ${my}.`]));
  const near=[],far=[];
  for(const X of G.units){if(X===u||X===inc.victim||(X.kind!=='sq'&&!X.isPlayer))continue;const S=u.sight[X.id]||[];
    if(S.some(s=>s.t>=inc.t-7&&s.t<=inc.t+2&&dist(s.x,s.y,inc.x,inc.y)<7))near.push(X);
    else{const f=S.find(s=>Math.abs(s.t-inc.t)<3&&dist(s.x,s.y,inc.x,inc.y)>10);if(f)far.push([X,zoneAt(f.x,f.y)])}}
  const nm=X=>X===asker?'you':X.name;
  if(near.length)L.push(`Right before, I saw ${listNames(near.map(nm))} near the ${inc.zone}.`);else L.push(`I didn't see any of ours near the ${inc.zone}.`);
  if(far.length){const [X,z]=pick(far);L.push(X===asker?`You were at the ${z} — I could see you.`:`${X.name} was at the ${z}; I could see them.`)}
  return L.join(' ')}
function doArrestStart(p){if(!p.isCom||p.arrestHold)return;if(p.arrestsLeft<=0){logMsg('You have no authority left for more arrests.','',p);return}const u=nearestArrestable(p,1.9);if(!u)return;p.arrestHold={T:u,t:0};say(u,'Comrade Commissar?',1.4)}
function completeArrest(p,u){
  p.arrestsLeft--;if(!G.comKnown){G.comKnown=true;logMsg(`${p.name} shows commissar's papers. Everyone knows who the commissar is now — including the spy.`,'bad')}G.comGuess[p.id]=100;
  if(u.isSpy){reveal(u,'resisted arrest',p);if(p===G.me)sfx('alarm');return}
  u.arrested=true;u.alive=false;u.post=null;for(const h of G.humans)if(h.arrestHold&&h.arrestHold.T===u)h.arrestHold=null;
  logMsg(`${u.name} is led away to the rear. ${u.name} was not the spy.`,'bad');
  noteTo(p,`You arrested ${u.name}. Under questioning it was clear ${u.name} was loyal. ${p.arrestsLeft} arrest${p.arrestsLeft===1?'':'s'} left.`,'key');
  banner('Wrong arrest',`${u.name} was not the spy. One rifle fewer on the line.`,'bad',3.6,h=>h!==u);
  if(u.isPlayer){banner('Arrested',`Commissar ${p.name} has taken you to the rear. You can watch the rest of the battle.`,'bad',5,u);allHumansDown()}}
function reveal(u,why,by){
  if(u.revealed)return;u.revealed=true;u.side='traitor';u.seeking=false;u.stab=null;u.fleeSet=false;u.path=[];u.repathT=0;u.sortie=false;
  if(u.wpn==='ptrd')u.wpn='mp40';u.mag=WPN[u.wpn].mag;
  if(!u.isPlayer)say(u,pick(['Verdammt!','Scheiße!']),2.5);
  logMsg(`${by&&by!==G.me?by.name+': ':''}Traitor! ${u.name} ${why}!`,'bad');
  noteAll(`${u.name} ${why}. ${u.name} is the spy and is running for the German lines.`,'key',h=>h!==u);
  banner('Traitor unmasked',`${u.name} is the spy. Stop ${u.isPlayer?'them':'him'} before ${u.isPlayer?'they reach':'he reaches'} the German lines!`,'good',4.5,h=>h!==u);
  if(u.isPlayer){banner('Exposed','Your cover is blown. Run for the German lines — reach the west edge of the map.','bad',5,u);if(u===G.me)sfx('alarm')}}
function playerFlare(p,tx,ty){
  if(!p.isSpy||p.revealed)return;
  if(G.phase!=='wave'){logMsg('Save the flare for when the Germans attack.','',p);return}
  if(p.flares<=0){logMsg('No flares left this assault.','',p);return}
  const w=noticedBy(p,null);p.flares--;doFlare(p,clamp(tx,1,W-2),clamp(ty,1,H-2));
  if(w.length){say(w[0],'Traitor!',2.5);reveal(p,'fired a green flare for the Germans',w[0])}}
function playerGrenade(p,tx,ty){if(p.grenades<=0)return;p.grenades--;throwGrenade(p,tx,ty,'rgd')}

// ================= the AI investigator's suspicion =================
function addS(u,v){G.susp[u.id]=Math.max(0,(G.susp[u.id]||0)+v)}
function sightNear(x,y,t,win,r,val){for(const B of liveSquad()){for(const X of liveSov()){if(X===B)continue;const S=B.sight[X.id]||[];if(S.some(s=>Math.abs(s.t-t)<=win&&dist(s.x,s.y,x,y)<r))addS(X,val)}}}
function carriers(cal){return liveSov().filter(x=>WPN[x.isPlayer?'ppsh':x.wpn].cal===cal)}
function processSuspicion(){
  const off=investigator();if(!off)return;const tag=off.isCom&&!G.comKnown?'The commissar\'s inquiry':off.name;
  for(const i of G.incidents){if(i.processed)continue;i.processed=true;
    if(i.type==='death'){const b=i.body;let said=null;
      if(b.cause==='bullet'&&b.dirKey!=='front'&&SOV_CALS.includes(b.cal)){const car=carriers(b.cal);car.forEach(x=>addS(x,60/Math.max(1,car.length)));said=`${i.victimName} took a ${b.cal} round from behind. Only ${listNames(car.map(x=>x.name))||'the dead'} carry that.`}
      else if(b.cause==='bullet'&&b.dirKey==='behind'){for(const h of G.humans)if(h.seenCaptured&&h.alive)addS(h,45);liveSov().forEach(x=>addS(x,5));said=`${i.victimName} was shot from behind with a German ${b.cal} round. Someone is using a captured gun.`}
      else if(b.cause==='grenade'&&b.gkind==='rgd'){liveSov().forEach(x=>addS(x,8));said=`${i.victimName} was killed by one of our own grenades.`}
      if(said){sightNear(i.x,i.y,i.t,6,7,22);logMsg(`${tag}: ${said}`,'bad')}}
    else if(i.type==='flare'){sightNear(i.x,i.y,i.t,4,5,30);logMsg(`${tag}: someone fired that green flare from the ${i.zone}.`,'bad')}
    else if(i.type==='hit'){const car=carriers(i.cal);car.forEach(x=>addS(x,25/Math.max(1,car.length)));sightNear(i.x,i.y,i.t,4,7,10)}}}
function officerArrest(){
  const off=investigator();if(!off||G.aiArrests<=0)return;
  const pool=liveSov().filter(u=>u!==off);if(!pool.length)return;let top=null,tv=0;for(const u of pool){const v=G.susp[u.id]||0;if(v>tv){tv=v;top=u}}
  if(!top||tv<80)return;G.aiArrests--;
  if(off.isCom&&!G.comKnown){G.comKnown=true;G.comGuess[off.id]=100;noteAll(`${off.name} showed commissar's papers and made an arrest. ${off.name} is the commissar.`,'key')}
  const tag=offTag(off);
  if(top.isPlayer){logMsg(`${tag}: ${top.name}, hand over your weapon. You are under arrest.`,'bad');
    if(G.humans.length===1){G.sched.push({at:G.time+1.5,k:'end',sw:!top.isSpy,txt:'arrested',tag});return}
    if(top.isSpy){reveal(top,'resisted arrest',off);return}
    G.sched.push({at:G.time+1.5,k:'arrestOut',u:top,tag});return}
  if(top.isSpy){logMsg(`${tag}: ${top.name}, you are under arrest.`,'good');reveal(top,'resisted arrest',off);return}
  top.arrested=true;top.alive=false;G.susp[top.id]=0;logMsg(`${tag}: ${top.name}, you are under arrest.`,'bad');
  banner('An arrest',`${tag} arrested ${top.name}. Your cover holds.`,'good',3.6,h=>h.isSpy);
  banner('An arrest',`${tag} arrested ${top.name}. ${top.name} was not the spy.`,'bad',3.6,LOYAL);noteAll(`${tag} arrested ${top.name}, who turned out to be loyal.`,'key',LOYAL)}
// end-of-game texts; each is a function of the viewing player so one event reads right for everyone
const ENDTXT={
  arrested:e=>me=>me.isSpy?`${e.tag} put the evidence together and arrested you before the next assault.`:`${e.tag} arrested you on the evidence. You were loyal — the line fought on without you.`,
  sorties:e=>me=>me.isSpy?'Three sorties failed. The Germans knew every move the squad made, and the block fell. Mission accomplished.':'Three sorties have failed. The Germans knew every move the squad made, and the block is lost.'};

// ================= sorties (Avalon) =================
function nearPass(x,y){for(let r=0;r<6;r++)for(let dy=-r;dy<=r;dy++)for(let dx=-r;dx<=r;dx++){const tx=(x|0)+dx,ty=(y|0)+dy;if(passable(tx,ty)&&!blockedAt(tx+0.5,ty+0.5,0.3))return{x:tx+0.5,y:ty+0.5}}return{x,y}}
function nextLeader(){const L=G.order.length;for(let k=0;k<L;k++){const u=G.order[G.lead%L];G.lead++;if(u.alive&&u.side==='sov')return u}return roster()[0]}
const pubSc=u=>(G.pub[u.id]||0)*60;
function aiTeam(L,k){const pool=roster().filter(m=>m!==L);
  const sc=m=>L.isSpy?pubSc(m)*0.5+rnd()*30:pubSc(m)+(L.isCom?(G.susp[m.id]||0)*0.8:0)+rnd()*12;
  const ss=new Map(pool.map(m=>[m,sc(m)]));pool.sort((a,b)=>ss.get(a)-ss.get(b)||a.id-b.id);return[L,...pool.slice(0,k-1)]}
function aiVote(u,team){
  if(u.isSpy)return team.includes(u)||rnd()<0.3;
  const sc=m=>pubSc(m)+(u.isCom?(G.susp[m.id]||0)*0.8:0);
  let risk=0;for(const m of team)if(m!==u)risk=Math.max(risk,sc(m));
  const outs=roster().filter(m=>!team.includes(m)&&m!==u).map(sc);const minOut=outs.length?Math.min(...outs):0;
  if(risk>minOut+12)return false;
  if(!team.includes(u)&&rnd()<0.2)return false;
  return true}
function recHTML(u){const r=G.rec[u.id]||[];return r.map(x=>x==='ok'?'✓':'✗').join('')}
function trackHTML(cur){return SORTIES.map((s,i)=>{const r=G.track[i];return `<i class="${r||(i===cur?'cur':'')}" title="${esc(s.name)}">${r==='ok'?'✓':r==='bad'?'✗':i+1}</i>`}).join('')}
const nm=u=>u===G.me?`${u.name} (you)`:u.name;
// The council is part of the simulated world: every peer steps it identically, and players act on it only through
// input events ('p' propose, 'v' vote). The world itself is frozen while it sits.
function openCouncil(){const i=G.mi-1;G.council={i,def:SORTIES[i],tries:0,hist:[],stage:null,team:[],votes:{},t:0,k:0,lead:null,ok:false};councilPropose()}
function councilPropose(){
  const C=G.council;C.lead=nextLeader();C.k=Math.min(TEAM[C.i],roster().length);C.forced=C.tries>=2;C.votes={};C.team=[];C.ok=false;
  if(C.lead.isPlayer){C.stage='pick';C.t=45}else{C.team=aiTeam(C.lead,C.k);councilTeamSet()}}
function councilTeamSet(){
  const C=G.council;
  if(C.forced){C.hist.push(`${C.lead.name}: ${C.team.map(u=>u.name).join(', ')} — ordered out`);C.stage='result';C.ok=true;C.t=3;return}
  C.stage='vote';C.t=40;
  for(const u of roster())if(!u.isPlayer)C.votes[u.id]=aiVote(u,C.team);else if(u===C.lead)C.votes[u.id]=true}
function councilPick(p,ids){
  const C=G.council;if(!C||C.stage!=='pick'||C.lead!==p)return;
  const R=roster(),team=[];for(const id of ids){const u=R.find(x=>x.id===id);if(u&&!team.includes(u))team.push(u)}
  if(team.length!==C.k)return;C.team=team;councilTeamSet()}
function councilVote(p,v){const C=G.council;if(!C||C.stage!=='vote'||!p.alive||!roster().includes(p))return;C.votes[p.id]=v}
function councilTick(dt){
  const C=G.council;C.t-=dt;
  if(C.stage==='pick'){if(C.t<=0||!C.lead.alive){C.team=aiTeam(C.lead.alive?C.lead:roster()[0],C.k);councilTeamSet()}return}
  if(C.stage==='vote'){const R=roster();
    if(C.t>0&&!R.every(u=>C.votes[u.id]!==undefined))return;
    for(const u of R)if(C.votes[u.id]===undefined)C.votes[u.id]=true;
    const yes=R.filter(u=>C.votes[u.id]).length;C.ok=yes>R.length/2;C.yes=yes;C.no=R.length-yes;C.voters=R;
    C.hist.push(`${C.lead.name}: ${C.team.map(u=>u.name).join(', ')} — ${C.ok?'approved':'rejected'} ${yes}–${R.length-yes}`);
    if(!C.ok)C.tries++;C.stage='result';C.t=4;return}
  if(C.stage==='result'&&C.t<=0){if(C.ok)launchSortie();else councilPropose()}}
function launchSortie(){
  const C=G.council;G.council=null;
  const M=G.mission={i:C.i,def:C.def,st:'go',team:C.team.filter(u=>u.alive&&u.side==='sov'),prog:0,sab:0,sabBy:[],decided:[],sabT:{},tLeft:80,hist:C.hist};
  M.obj=nearPass(M.def.x,M.def.y);
  const n=2+M.i;for(let k=0;k<n;k++){let x=M.obj.x+(rnd()-.5)*6,y=M.obj.y+(rnd()-.5)*6;const sp=nearPass(clamp(x,12,34),clamp(y,1,38));const kind=rnd()<0.4?'smg':'rifle',wpn=kind==='smg'?'mp40':'kar98';
    G.units.push(mkUnit({kind,side:'ger',uniform:'ger',name:'German',wpn,mag:WPN[wpn].mag,x:sp.x,y:sp.y,aim:0,hp:100,maxhp:100,state:'hold',sentry:true,grenCd:12+rnd()*20}))}
  M.team.forEach((u,k)=>{u.sortie=true;if(u.isPlayer)return;const a=k/M.team.length*TAU;u.spot=nearPass(M.obj.x+1+Math.cos(a)*1.4,M.obj.y+Math.sin(a)*1.4);u.seeking=false;u.q=null;u.repathT=0;u.path=[];
    if(u.isSpy)u.stabCd=Math.min(u.stabCd,8+rnd()*8)});
  const onT=h=>M.team.includes(h);
  banner(`Sortie: ${M.def.name}`,'You are on the team. Follow the yellow marker into no-man\'s land.','',4,onT);
  banner(`Sortie: ${M.def.name}`,`The team moves out: ${M.team.map(u=>u.name).join(', ')}.`,'',4,h=>!onT(h));
  logMsg('Move out! Get to the marker and hold it while the work is done.','',onT);logMsg('Cover the sortie team from the line.','',h=>!onT(h));
  if(G.me)sfx('whistleAttack')}
function sortieTick(dt){
  const M=G.mission;M.tLeft-=dt;
  const live=M.team.filter(u=>u.alive&&u.side==='sov');if(!live.length){resolveSortie('lost');return}
  const geNear=G.units.some(g=>g.alive&&g.side==='ger'&&dist(g.x,g.y,M.obj.x,M.obj.y)<7);M.contested=geNear;
  const at=live.filter(u=>dist(u.x,u.y,M.obj.x,M.obj.y)<2.8);
  if(at.length&&!geNear)M.prog+=dt/8;
  for(const u of at)if(u.isSpy&&!u.isPlayer&&!u.revealed&&!M.decided.includes(u)&&M.prog>0.25){M.decided.push(u);if(rnd()<(M.i===0?0.5:0.9)){M.sab++;M.sabBy.push(u)}}
  // a human spy sabotages by holding X at the objective
  for(const p of at){if(!p.isPlayer||!p.isSpy||p.revealed||M.sabBy.includes(p))continue;
    if(p.btn&4){M.sabT[p.id]=(M.sabT[p.id]||0)+dt;
      if(M.sabT[p.id]>=1.5){M.sab++;M.sabBy.push(p);if(p===G.me)sfx('page');logMsg('You quietly cross two wires. Nobody will know which of you did it.','good',p);
        const w=noticedBy(p,null);if(w.length&&rnd()<0.5){addS(p,25);logMsg(`${w[0].name} glanced over at your hands.`,'bad',p)}}}else M.sabT[p.id]=0}
  if(M.prog>=1)resolveSortie('done');else if(M.tLeft<=0)resolveSortie('time')}
function resolveSortie(how){
  const M=G.mission;M.st='done';const ok=how==='done'&&M.sab===0;const T=M.team,names=listNames(T.map(u=>u.name));
  G.track[M.i]=ok?'ok':'bad';if(!ok)G.fails++;
  for(const u of T){u.sortie=false;u.repathT=0;u.seeking=false;(G.rec[u.id]=G.rec[u.id]||[]).push(ok?'ok':'bad')}
  for(const g of G.units)if(g.alive&&g.sentry){g.alive=false;g.gone=true}
  G.mod=ok?{mul:0.75,tank:M.def.tank?0.35:1}:{mul:1.2,mg:1,tank:1};
  if(how==='done'&&M.sab){for(const u of T){G.pub[u.id]=(G.pub[u.id]||0)+M.sab/T.length;addS(u,60*M.sab/T.length)}
    banner('Sortie sabotaged',`The charges were rigged. Someone on the team — ${T.map(u=>u.name).join(', ')} — is the spy.`,'bad',5);
    noteAll(`Sortie ${M.i+1} (${M.def.name}) was SABOTAGED. Team: ${names}. ${M.def.bad}`,'key')}
  else if(ok){for(const u of T)G.pub[u.id]=Math.max(0,(G.pub[u.id]||0)-0.12);banner('Sortie succeeded',M.def.ok,'good',4);noteAll(`Sortie ${M.i+1} (${M.def.name}) succeeded. Team: ${names}. ${M.def.ok}`,'talk')}
  else{banner('Sortie failed',how==='lost'?'The whole team was lost out there.':'The team could not finish before the Germans returned.','bad',4);noteAll(`Sortie ${M.i+1} (${M.def.name}) failed — ${how==='lost'?'the team was wiped out':'out of time'}. Team: ${names}.`,'death')}
  logMsg(`Sorties: ${G.track.filter(x=>x==='ok').length} succeeded, ${G.fails} failed.`,ok?'good':'bad');
  G.phaseT=G.wave===0?18:15;
  if(G.fails>=3)G.sched.push({at:G.time+2,k:'end',sw:true,txt:'sorties'})}

// ================= waves =================
function startWave(){
  G.wave++;G.phase='wave';const w=WAVES[G.wave-1];const q=[];
  const md=G.mod||{mul:1};G.mod=null;G.tankMul=md.tank||1;const n=v=>Math.max(0,Math.round(v*md.mul*G.diff.mul));
  for(let i=0;i<n(w.r);i++)q.push('rifle');for(let i=0;i<n(w.s);i++)q.push('smg');for(let i=0;i<n(w.g);i++)q.push('gren');shuffle(q);
  for(let i=0;i<w.m+(md.mg||0);i++)q.splice(1+i*3,0,'mg');if(w.t)q.splice(Math.floor(q.length*0.35),0,'tank');
  G.spawnQ=q;G.spawnT=0;G.arrestDone=false;G.pushed=false;G.lastSpawn=G.time;
  assignPosts();
  const sp=G.spy;if(!sp.isPlayer&&sp.alive&&!sp.revealed){sp.flaresLeft=G.wave>=2?1:0;sp.flareCd=25+rnd()*35;sp.stabCd=G.wave>=2?10+rnd()*20:1e9}
  for(const h of G.humans)if(h.isSpy)h.flares=1;
  banner(`Assault ${G.wave} of ${WAVES.length}`,w.txt,'',4);if(G.me)sfx('whistleAttack')}
function endWave(){
  if(G.wave>=WAVES.length){const sf=G.spyFate,arr=G.spy.arrested;
    endGame(false,me=>me.isSpy?'Dawn. Fresh troops are crossing the Volga and the line held. Your mission failed.':
      sf==='killed'?'Dawn. The line held, and the traitor is dead.':sf==='escaped'?'Dawn. The line held, but the spy got away to the Germans.':arr?'Dawn. The line held.':me.isCom?'Dawn. The line held, but the spy is still among you — and you never caught him.':'Dawn. The line held, but the spy is still among you.');return}
  G.phase='lull';G.phaseT=15;
  for(const u of liveSov())u.hp=u.maxhp;
  for(const k in G.comGuess)G.comGuess[k]=Math.max(0,G.comGuess[k]-8);
  banner('Assault beaten back','The Germans are pulling back. Restock — the squad will pick a sortie team shortly.','good',3.5);
  processSuspicion();
  G.bodies=G.bodies.filter(b=>b.uniform==='sov'||G.time-b.t<150||(b.wpn&&!b.taken))}
function phaseTick(dt){
  if(G.phase==='lull'){
    if(G.mi===G.wave&&G.mi<SORTIES.length){G.councilT=(G.councilT===undefined?4:G.councilT)-dt;if(G.councilT<=0){G.councilT=undefined;G.mi++;openCouncil()}return}
    if(G.mission&&G.mission.st==='go'){sortieTick(dt);return}
    G.phaseT-=dt;if(!G.arrestDone&&G.phaseT<5&&G.wave>0){G.arrestDone=true;officerArrest()}if(G.phaseT<=0)startWave()}
  else{G.spawnT-=dt;if(G.spawnQ.length&&G.spawnT<=0){spawnGerman(G.spawnQ.shift());if(G.spawnQ.length&&G.spawnQ[0]!=='tank'&&rnd()<0.35)spawnGerman(G.spawnQ.shift());G.spawnT=0.6+rnd()*1.0;G.lastSpawn=G.time}
    const since=G.time-(G.lastSpawn||G.time);
    if(!G.spawnQ.length&&since>110&&!G.pushed){G.pushed=true;for(const u of G.units)if(u.alive&&u.side==='ger'&&u.kind!=='tank'&&u.kind!=='mg')assault(u)}
    if(!G.spawnQ.length&&since>200){for(const u of G.units)if(u.alive&&u.side==='ger'){u.alive=false;u.gone=true}logMsg('The last Germans fall back into the ruins.')}
    if(!G.spawnQ.length&&!G.units.some(u=>u.alive&&u.side==='ger'))endWave()}}
function overrunTick(dt){
  if(G.units.some(u=>u.alive&&u.side==='ger'&&u.kind!=='tank'&&inDugout(u)))G.overrun+=dt;else G.overrun=Math.max(0,G.overrun-dt*0.5);
  if(G.overrun>=8){endGame(true,me=>me.isSpy?'The Germans stormed the command dugout. The position has fallen, and nobody knows it was you.':'The Germans stormed the command dugout. The position has fallen.');return}
  if(!G.people.some(u=>u.alive&&u.side==='sov'&&!u.isSpy))endGame(true,'The last of the loyal defenders is gone. The block belongs to the Germans.')}

// ================= update =================
function unitCommon(u,dt){
  if(u.fireCd>0)u.fireCd-=dt;
  if(u.reloadT>0){u.reloadT-=dt;if(u.reloadT<=0){u.reloadT=0;const w=WPN[u.wpn];if(u.isPlayer){const take=Math.min(w.mag-u.mag,u.reserve);u.mag+=take;u.reserve-=take}else u.mag=w.mag}}
  if(u.bark){u.bark.life-=dt;if(u.bark.life<=0)u.bark=null}
  if(u.kind==='sq'&&u.side==='sov'){
    u.logT-=dt;if(u.logT<=0){u.logT=0.5;u.plog.push({t:G.time,x:u.x,y:u.y});if(u.plog.length>900)u.plog.splice(0,200)}
    u.sightT-=dt;if(u.sightT<=0){u.sightT=0.4;for(const o of G.units){if(o===u||!o.alive||(o.side!=='sov'&&o.side!=='traitor')||(o.kind!=='sq'&&!o.isPlayer))continue;if(dist(u.x,u.y,o.x,o.y)>12||!los(u.x,u.y,o.x,o.y,0.35))continue;const a=u.sight[o.id]||(u.sight[o.id]=[]);a.push({t:G.time,x:o.x,y:o.y});if(a.length>500)a.splice(0,150);
      if(o.isPlayer&&o.isSpy&&o.slot===1&&!o.seenCaptured){o.seenCaptured=true;addS(o,10);logMsg(`${u.name}: ${o.name}, where did you get that German gun?`)}}}}}
function separate(){const L=G.units;for(let i=0;i<L.length;i++){const a=L[i];if(!a.alive)continue;for(let j=i+1;j<L.length;j++){const b=L[j];if(!b.alive)continue;if(a.path.length&&b.path.length&&a.kind!=='tank'&&b.kind!=='tank')continue;const r=(a.kind==='tank'||b.kind==='tank')?1.5:0.55;const dx=b.x-a.x,dy=b.y-a.y;const d=Math.hypot(dx,dy);if(d>0.001&&d<r){const push=(r-d)/2;const nx=dx/d,ny=dy/d;
  if(a.kind!=='tank'&&!blockedAt(a.x-nx*push,a.y-ny*push,0.28)){a.x-=nx*push;a.y-=ny*push}if(b.kind!=='tank'&&!blockedAt(b.x+nx*push,b.y+ny*push,0.28)){b.x+=nx*push;b.y+=ny*push}}}}}
// One deterministic simulation tick. `inputs[i]` is the input record of human seat i for this tick.
const DT=1/30;
function step(inputs){
  if(!G||G.over)return;
  G.tick++;const dt=DT;
  for(const u of G.units){u.ox=u.x;u.oy=u.y}for(const p of G.proj){p.ox=p.x;p.oy=p.y}
  if(G.council){for(let i=0;i<G.humans.length;i++){const h=G.humans[i],I=inputs&&inputs[i];h.btn=0;if(I&&I[4])for(const e of I[4])humanEvent(h,e)}councilTick(dt);return}
  G.time+=dt;
  for(const s of G.sched)if(!s.done&&G.time>=s.at){s.done=true;runSched(s);if(G.over)return}G.sched=G.sched.filter(s=>!s.done);
  phaseTick(dt);if(G.over||G.council)return;
  for(let i=0;i<G.humans.length;i++){humanTick(G.humans[i],inputs?inputs[i]:null,dt);if(G.over)return}
  for(const u of G.units){if(!u.alive)continue;unitCommon(u,dt);if(u.isPlayer)continue;if(u.kind==='tank')tankAI(u,dt);else if(u.side==='ger')gerAI(u,dt);else sovAI(u,dt);if(G.over)return}
  separate();updateProj(dt);if(G.over)return;updateNades(dt);if(G.over)return;overrunTick(dt)}
function updateFx(dt){
  for(const f of G.fx)f.t+=dt;G.fx=G.fx.filter(f=>f.t<f.life);
  for(const s of G.smoke){s.t+=dt;s.x+=s.vx*dt;s.y+=s.vy*dt;s.r+=dt*0.35}G.smoke=G.smoke.filter(s=>s.t<s.life);
  G.fireT=(G.fireT||0)-dt;if(G.fireT<=0){G.fireT=0.35;for(const f of FIRES)if(crnd()<0.5)G.smoke.push({x:f.x+(crnd()-.5)*.6,y:f.y+(crnd()-.5)*.6,r:0.4,t:0,life:4+crnd()*3,vx:0.5+crnd()*0.3,vy:-0.15+crnd()*0.1})}
  if(G.smoke.length>220)G.smoke.splice(0,G.smoke.length-220);
  G.shake*=Math.pow(0.03,dt);if(G.shake<0.2)G.shake=0;G.kick*=Math.pow(0.001,dt);
  for(const h of G.hitInd)h.t+=dt;G.hitInd=G.hitInd.filter(h=>h.t<h.life);if(G.dmgFlash>0)G.dmgFlash-=dt;
  G.ambT=(G.ambT||4)-dt;if(G.ambT<=0){G.ambT=6+crnd()*12;if(state==='play'){sfx('distant');G.shake=Math.max(G.shake,REDUCED?0:2)}}
  if(G.banner){G.banner.life-=dt;if(G.banner.life<=0){G.banner=null;$('banner').hidden=true}}}

// ================= bake & render =================
let MAPC=null,MG=null;const S=32;
function bake(){
  const c=document.createElement('canvas');c.width=W*S;c.height=H*S;const g=c.getContext('2d');const R=mulberry(77);
  for(let y=0;y<H;y++)for(let x=0;x<W;x++){const px=x*S,py=y*S,t=grid[y*W+x];
    if(t===WATER){g.fillStyle='#1d2a33';g.fillRect(px,py,S,S);for(let k=0;k<3;k++){g.fillStyle=`rgba(150,180,200,${0.04+R()*0.06})`;g.fillRect(px+R()*S,py+R()*S,6+R()*14,1.5)}if(R()<0.12){g.fillStyle='rgba(215,225,230,.55)';g.beginPath();g.ellipse(px+R()*S,py+R()*S,4+R()*7,2+R()*4,R()*3,0,TAU);g.fill()}continue}
    let base;const inB=x>=42&&x<=52&&y>=9&&y<=30,dug=x>=55&&x<=56&&y>=17&&y<=22;const street=y>=18&&y<=22&&x<=41;
    if(t===FLOOR||t===WIN||t===CRATE){base=dug?'#5a4630':inB?'#4b453c':'#423c35'}
    else if(x>=57)base='#5a5448';else if(street)base='#45423c';else if(x>=39&&x<=41&&(y<=8||y>=31))base='#352c22';else base='#423b32';
    g.fillStyle=base;g.fillRect(px,py,S,S);
    if(street&&t===GROUND){g.strokeStyle='rgba(0,0,0,.25)';g.lineWidth=1;for(let k=0;k<4;k++)g.strokeRect(px+(k%2)*16+.5,py+(k>>1)*16+.5,16,16)}
    else if(dug){g.fillStyle='rgba(0,0,0,.3)';for(let k=0;k<4;k++)g.fillRect(px,py+k*8,S,1.2)}
    else if(inB){g.strokeStyle='rgba(0,0,0,.18)';g.strokeRect(px+.5,py+.5,S,S);if(R()<0.3){g.fillStyle='rgba(90,80,70,.6)';for(let k=0;k<4;k++)g.fillRect(px+R()*S,py+R()*S,2+R()*4,2+R()*3)}}
    else{for(let k=0;k<6;k++){g.fillStyle=R()<0.55?`rgba(230,228,220,${0.08+R()*0.16})`:'rgba(0,0,0,.18)';const s=1+R()*4;g.fillRect(px+R()*S,py+R()*S,s,s*0.7)}}}
  g.strokeStyle='rgba(150,150,145,.35)';g.lineWidth=2;for(const ry of [19.6,20.4]){g.beginPath();g.moveTo(0,ry*S);g.lineTo(42*S,ry*S);g.stroke()}
  for(let i=0;i<34;i++){const x=(19+R()*18),y=1+R()*38;if(get(x|0,y|0)!==GROUND)continue;craterAt(g,x*S,y*S,(0.6+R()*1.0)*S)}
  g.strokeStyle='rgba(160,150,140,.55)';g.lineWidth=1;for(const [y0,y1] of [[1,16],[24,38]]){g.beginPath();for(let y=y0;y<=y1;y+=0.25){const x=35.6+Math.sin(y*9)*0.18;y===y0?g.moveTo(x*S,y*S):g.lineTo(x*S,y*S)}g.stroke();for(let y=y0;y<=y1;y+=1.2){const x=35.6*S,yy=y*S;g.beginPath();g.moveTo(x-6,yy-6);g.lineTo(x+6,yy+6);g.moveTo(x+6,yy-6);g.lineTo(x-6,yy+6);g.stroke()}}
  for(let y=0;y<H;y++)for(let x=0;x<W;x++){if(grid[y*W+x]===WALL){g.fillStyle='rgba(0,0,0,.4)';g.fillRect(x*S+7,y*S+7,S,S)}}
  for(let y=0;y<H;y++)for(let x=0;x<W;x++){const t=grid[y*W+x],px=x*S,py=y*S;
    if(t===WALL){const ger=x<42;g.fillStyle=ger?'#5a4a3f':'#634537';g.fillRect(px,py,S,S);g.fillStyle=ger?'#6b594c':'#77543f';g.fillRect(px+3,py+3,S-6,S-6);g.strokeStyle='rgba(25,15,10,.45)';g.lineWidth=1;for(let r=0;r<4;r++){const yy=py+3+r*6.5;g.beginPath();g.moveTo(px+3,yy);g.lineTo(px+S-3,yy);g.stroke()}
      if(R()<0.3){g.fillStyle='rgba(20,15,12,.5)';g.beginPath();g.arc(px+R()*S,py+R()*S,2+R()*4,0,TAU);g.fill()}}
    else if(t===WIN){const vert=get(x,y-1)===WALL||get(x,y+1)===WALL||get(x,y-1)===WIN||get(x,y+1)===WIN;g.fillStyle='#77543f';if(vert){g.fillRect(px+3,py,S-6,5);g.fillRect(px+3,py+S-5,S-6,5);g.fillStyle='#5b4330';g.fillRect(px+5,py+5,S-10,S-10);g.fillStyle='rgba(190,210,220,.35)';g.fillRect(px+8,py+8,3,4);g.fillRect(px+18,py+20,4,3)}else{g.fillRect(px,py+3,5,S-6);g.fillRect(px+S-5,py+3,5,S-6);g.fillStyle='#5b4330';g.fillRect(px+5,py+5,S-10,S-10)}}
    else if(t===COVER){const k=ck[y*W+x];
      if(k===1){for(let r=0;r<3;r++)for(let i=0;i<2;i++){const bx=px+4+i*13+(r%2)*3,by=py+5+r*9;g.fillStyle='rgba(0,0,0,.35)';g.beginPath();g.ellipse(bx+8,by+5,8,5,0,0,TAU);g.fill();g.fillStyle=(r+i)%2?'#a08d64':'#93815b';g.beginPath();g.ellipse(bx+6,by+3,8,5,0,0,TAU);g.fill();g.strokeStyle='#3d3322';g.lineWidth=1;g.stroke()}}
      else if(k===3){g.fillStyle='rgba(0,0,0,.4)';g.fillRect(px+3,py+5,S,S-6);g.fillStyle='#2b2826';g.fillRect(px,py+3,S,S-8);g.fillStyle='#5e3a26';g.fillRect(px+4,py+7,S-10,6);g.fillStyle='#1a1817';g.beginPath();g.arc(px+8,py+S-6,5,0,TAU);g.arc(px+S-8,py+S-6,5,0,TAU);g.fill()}
      else{for(let i=0;i<7;i++){g.fillStyle=['#6d645b','#7b5847','#5b544c','#857a6c'][i%4];g.beginPath();const cx=px+4+R()*(S-8),cy=py+4+R()*(S-8),r=3+R()*6;g.moveTo(cx+r,cy);for(let a=1;a<6;a++)g.lineTo(cx+Math.cos(a*1.2)*r*(0.6+R()*0.5),cy+Math.sin(a*1.2)*r*(0.6+R()*0.5));g.closePath();g.fill()}}}
    else if(t===CRATE){g.fillStyle='rgba(0,0,0,.4)';g.fillRect(px+5,py+6,S-6,S-6);g.fillStyle='#6b5233';g.fillRect(px+3,py+3,S-6,S-6);g.strokeStyle='#2c2015';g.lineWidth=1.5;g.strokeRect(px+3.5,py+3.5,S-7,S-7);g.beginPath();g.moveTo(px+3,py+S/2);g.lineTo(px+S-3,py+S/2);g.stroke();g.fillStyle='#e5dcc0';g.font='8px "PT Mono", monospace';g.fillText('7.62',px+7,py+13)}}
  g.save();g.translate(53.4*S,31.5*S);g.rotate(-Math.PI/2);g.font='15px "Russo One", Impact, sans-serif';g.fillStyle='rgba(205,70,45,.6)';g.fillText('ЗА ВОЛГОЙ ДЛЯ НАС ЗЕМЛИ НЕТ',0,0);g.restore();
  g.font='13px "Russo One", Impact, sans-serif';g.fillStyle='rgba(230,220,200,.14)';g.fillText('ШТАБ',54.9*S,20.2*S);
  MAPC=c;MG=g}
function craterAt(g,x,y,r){const gr=g.createRadialGradient(x,y,0,x,y,r);gr.addColorStop(0,'rgba(15,12,10,.75)');gr.addColorStop(0.65,'rgba(30,25,20,.55)');gr.addColorStop(0.85,'rgba(95,85,72,.45)');gr.addColorStop(1,'rgba(95,85,72,0)');g.fillStyle=gr;g.beginPath();g.arc(x,y,r,0,TAU);g.fill()}
function decal(k,x,y,r){if(!MG)return;if(k==='crater')craterAt(MG,x*S,y*S,(r||2)*S*0.45);else if(k==='blood'){MG.fillStyle='rgba(70,10,8,.55)';MG.beginPath();MG.arc(x*S,y*S,2+crnd()*3,0,TAU);MG.fill()}else if(k==='pool'){MG.fillStyle='rgba(60,8,6,.5)';MG.beginPath();MG.ellipse(x*S,y*S,10+crnd()*6,7+crnd()*4,crnd()*3,0,TAU);MG.fill()}}

function resize(){DPR=Math.min(2,window.devicePixelRatio||1);const r=$('app').getBoundingClientRect();VW=r.width;VH=r.height;cv.width=Math.round(VW*DPR);cv.height=Math.round(VH*DPR);fog.width=cv.width;fog.height=cv.height;TS=clamp(Math.min(VW,VH)/(VW<600?14:20),24,40)}
window.addEventListener('resize',resize);
const w2s=(x,y)=>[x*TS-camX,y*TS-camY];
function drawSoldier(g,x,y,s,u){
  g.save();g.translate(x,y);const sov=u.uniform==='sov';
  g.fillStyle='rgba(0,0,0,.35)';g.beginPath();g.ellipse(s*0.06,s*0.08,s*0.36,s*0.3,0,0,TAU);g.fill();
  if(sov){g.strokeStyle=u.revealed?'#ff4a2a':u.col;g.lineWidth=Math.max(2,s*0.07);g.beginPath();g.arc(0,0,s*0.43,0,TAU);g.stroke()}
  g.rotate(u.aim);
  const bob=u.moving?Math.sin(u.phase)*s*0.04:0;
  g.fillStyle=sov?'#5c5139':'#4b4f44';rr(g,-s*0.38,-s*0.17,s*0.16,s*0.34,s*0.05);g.fill();
  g.fillStyle=sov?'#7b6f4c':'#5c6555';g.strokeStyle='#15130f';g.lineWidth=Math.max(1,s*0.04);g.beginPath();g.ellipse(0,bob,s*0.21,s*0.34,0,0,TAU);g.fill();g.stroke();
  const w=WPN[u.wpn]||WPN.ppsh,len=w.len*s;const wood=w.snd==='rifle'||w.snd==='rifle2'||u.wpn==='ptrd';
  g.fillStyle=wood?'#5a3e26':'#2a2724';g.fillRect(s*0.05,s*0.07,len*0.45,s*0.08);g.fillStyle='#2a2724';g.fillRect(s*0.05+len*0.4,s*0.08,len*0.6,s*0.055);
  if(u.wpn==='ppsh'){g.fillStyle='#24211e';g.beginPath();g.arc(s*0.3,s*0.14,s*0.08,0,TAU);g.fill()}
  if(u.wpn==='dp'||u.wpn==='mg42'){g.fillStyle='#24211e';g.beginPath();g.arc(s*0.32,s*0.06,s*0.1,0,TAU);g.fill()}
  g.fillStyle='#d9a882';g.beginPath();g.arc(s*0.22,s*0.15,s*0.055,0,TAU);g.arc(s*0.42,s*0.1,s*0.05,0,TAU);g.fill();
  if(sov){g.fillStyle='#4b5a35';g.beginPath();g.arc(s*0.02,0,s*0.2,0,TAU);g.fill();g.stroke();g.fillStyle='rgba(255,255,255,.14)';g.beginPath();g.arc(-s*0.03,-s*0.06,s*0.08,0,TAU);g.fill();g.fillStyle='#c8412b';g.beginPath();g.arc(s*0.15,0,s*0.035,0,TAU);g.fill()}
  else{g.fillStyle='#3f453a';g.beginPath();g.arc(s*0.02,0,s*0.25,0,TAU);g.fill();g.stroke();g.fillStyle='#545b4d';g.beginPath();g.arc(s*0.02,0,s*0.19,0,TAU);g.fill();g.fillStyle='rgba(255,255,255,.1)';g.beginPath();g.arc(-s*0.03,-s*0.06,s*0.07,0,TAU);g.fill()}
  g.restore()}
function drawBody(g,x,y,s,b){g.save();g.translate(x,y);g.rotate(b.aim+Math.PI/2);const sov=b.uniform==='sov';
  g.fillStyle=sov?'#6c6244':'#525a4b';g.strokeStyle='#15130f';g.lineWidth=Math.max(1,s*0.04);g.beginPath();g.ellipse(0,s*0.05,s*0.2,s*0.38,0,0,TAU);g.fill();g.stroke();
  g.fillStyle=sov?'#4b5a35':'#3f453a';g.beginPath();g.arc(s*0.05,-s*0.42,s*0.17,0,TAU);g.fill();g.stroke();
  if(!b.taken){g.fillStyle='#4a3a28';g.fillRect(s*0.25,-s*0.1,s*0.07,s*0.6)}
  if(sov&&b.u&&b.u.col){g.fillStyle=b.u.col;g.fillRect(-s*0.2,-s*0.12,s*0.4,s*0.06)}
  g.restore()}
function drawTank(g,x,y,s,u){g.save();g.translate(x,y);
  g.fillStyle='rgba(0,0,0,.4)';g.fillRect(-s*1.25+6,-s*0.85+6,s*2.5,s*1.7);
  g.fillStyle='#24231f';g.fillRect(-s*1.3,-s*0.95,s*2.6,s*0.38);g.fillRect(-s*1.3,s*0.57,s*2.6,s*0.38);
  g.fillStyle='#3a3934';const tp=(u.phase*s*0.2)%(s*0.25);for(let i=0;i<11;i++){const xx=-s*1.3+((i*s*0.25+tp)%(s*2.6));g.fillRect(xx,-s*0.95,2,s*0.38);g.fillRect(xx,s*0.57,2,s*0.38)}
  g.fillStyle=u.dead?'#2b2a27':'#5d6156';g.strokeStyle='#121210';g.lineWidth=2;g.fillRect(-s*1.15,-s*0.6,s*2.3,s*1.2);g.strokeRect(-s*1.15,-s*0.6,s*2.3,s*1.2);
  g.fillStyle=u.dead?'#232220':'#4d5148';g.fillRect(-s*1.1,-s*0.45,s*0.6,s*0.9);
  g.rotate(u.turret||0);g.fillStyle=u.dead?'#2a2926':'#676b5f';rr(g,-s*0.5,-s*0.45,s*1.0,s*0.9,s*0.12);g.fill();g.stroke();g.fillStyle='#2b2b28';g.fillRect(s*0.45,-s*0.07,s*1.3,s*0.14);g.beginPath();g.arc(-s*0.15,0,s*0.16,0,TAU);g.fill();
  if(!u.dead&&u.hp<u.maxhp){g.rotate(-(u.turret||0));g.fillStyle='rgba(0,0,0,.6)';g.fillRect(-s,-s*1.25,s*2,4);g.fillStyle='#d8aa4d';g.fillRect(-s,-s*1.25,s*2*u.hp/u.maxhp,4)}
  g.restore()}
function render(){
  ctx.setTransform(DPR,0,0,DPR,0,0);ctx.fillStyle='#0b0a09';ctx.fillRect(0,0,VW,VH);
  if(!G||!MAPC)return;const tm=performance.now()/1000;const me=G.me;const playing=!!me&&state!=='title';
  // dead players spectate: the camera follows a living comrade and the fog lifts
  let p=me;if(playing&&!me.alive){let best=null,bd=1e9;for(const u of G.people)if(u.alive&&u.side==='sov'){const d=dist(u.x,u.y,me.x,me.y);if(d<bd){bd=d;best=u}}if(best)p=best}
  const eye=playing&&me.alive?me:null;const playerSeesPt=(x,y)=>!eye||seesPt(eye,x,y);
  let cx,cy;
  if(playing){let lx=0,ly=0;if(!eye){}else if(!TOUCH){lx=clamp(((MOUSE.x-VW/2)/TS)*0.28,-5,5);ly=clamp(((MOUSE.y-VH/2)/TS)*0.28,-4,4)}else{lx=Math.cos(p.aim)*3;ly=Math.sin(p.aim)*2}cx=p.x+lx;cy=p.y+ly}
  else{const t=tm*0.03;cx=36+Math.sin(t)*12;cy=20+Math.sin(t*1.3)*8}
  const sh=G.shake;camX=cx*TS-VW/2+(sh?(crnd()-.5)*sh:0);camY=cy*TS-VH/2+(sh?(crnd()-.5)*sh:0);
  camX=clamp(camX,-3*TS,W*TS-VW+3*TS);camY=clamp(camY,-3*TS,H*TS-VH+3*TS);
  ctx.drawImage(MAPC,-camX,-camY,W*TS,H*TS);
  {const [wx]=w2s(60,0);if(wx<VW){ctx.save();ctx.globalAlpha=0.12;ctx.strokeStyle='#9fb8c8';ctx.lineWidth=1;for(let i=0;i<14;i++){const yy=((i*61+tm*14)%(H*TS))-camY;const xx=wx+((i*37)%(4*TS));ctx.beginPath();ctx.moveTo(xx,yy);ctx.lineTo(xx+TS*0.8,yy);ctx.stroke()}ctx.restore()}}
  const vis=u=>!playing||u===me||playerSeesPt(u.x,u.y);
  const on=(sx,sy,m)=>sx>-m&&sy>-m&&sx<VW+m&&sy<VH+m;
  for(const b of G.bodies){if(playing&&!playerSeesPt(b.x,b.y))continue;const [sx,sy]=w2s(b.x,b.y);if(!on(sx,sy,50))continue;drawBody(ctx,sx,sy,TS,b);
    if(eye&&b.uniform==='sov'&&!b.inspBy.includes(me.id)&&!me.isSpy&&b.u!==me){ctx.fillStyle='rgba(216,170,77,.9)';ctx.font=`700 ${Math.max(11,TS*0.34)|0}px "PT Sans", sans-serif`;ctx.textAlign='center';ctx.fillText('?',sx,sy-TS*0.55)}}
  for(const u of G.units){if(u.kind==='tank'&&(u.alive||u.dead)){const [sx,sy]=w2s(u.x,u.y);if(u.dead||vis(u))drawTank(ctx,sx,sy,TS,u)}}
  for(const n of G.nades){const [sx,sy]=w2s(n.x,n.y);if(playing&&!playerSeesPt(n.x,n.y))continue;ctx.fillStyle='rgba(0,0,0,.4)';ctx.beginPath();ctx.arc(sx,sy,TS*0.08,0,TAU);ctx.fill();ctx.fillStyle=n.kind==='stick'?'#6b6a5a':'#3d4a32';ctx.beginPath();ctx.arc(sx,sy-n.z*TS*0.9,TS*0.1,0,TAU);ctx.fill();if(n.t>n.T&&Math.sin(tm*30)>0){ctx.strokeStyle='rgba(255,200,120,.7)';ctx.lineWidth=1.5;ctx.beginPath();ctx.arc(sx,sy,TS*0.28,0,TAU);ctx.stroke()}}
  for(const u of G.units){if(!u.alive||u.kind==='tank'||!vis(u))continue;const [sx,sy]=w2s(u.x,u.y);if(!on(sx,sy,60))continue;drawSoldier(ctx,sx,sy,TS,u);
    if(u.isPlayer){ctx.strokeStyle=u===me?'rgba(255,255,255,.85)':'rgba(255,255,255,.35)';ctx.lineWidth=1.5;ctx.beginPath();ctx.arc(sx,sy,TS*0.53,0,TAU);ctx.stroke()}}
  ctx.lineCap='round';for(const pr of G.proj){const [sx,sy]=w2s(pr.x,pr.y);if(!on(sx,sy,40))continue;const L=pr.he?0.5:0.9;ctx.strokeStyle=pr.he?'rgba(255,180,90,.9)':pr.side==='ger'?'rgba(255,190,140,.85)':'rgba(255,240,170,.85)';ctx.lineWidth=pr.he?3:pr.at?2.5:1.5;ctx.beginPath();ctx.moveTo(sx-pr.dx*TS*L,sy-pr.dy*TS*L);ctx.lineTo(sx,sy);ctx.stroke()}
  for(const f of G.fx){if(f.k==='flare')continue;const [sx,sy]=w2s(f.x,f.y);if(!on(sx,sy,200))continue;const k=f.t/f.life;
    if(f.k==='muz'){ctx.save();ctx.translate(sx,sy);ctx.rotate(f.a);ctx.fillStyle=`rgba(255,230,150,${1-k})`;const L=(f.big?0.9:0.35)*TS;ctx.beginPath();ctx.moveTo(0,-L*0.25);ctx.lineTo(L,0);ctx.lineTo(0,L*0.25);ctx.closePath();ctx.fill();ctx.restore()}
    else if(f.k==='dust'){ctx.fillStyle=`rgba(150,140,125,${0.5*(1-k)})`;ctx.beginPath();ctx.arc(sx,sy,TS*(0.1+k*0.3),0,TAU);ctx.fill()}
    else if(f.k==='spark'){ctx.fillStyle=`rgba(255,220,140,${1-k})`;for(let i=0;i<(f.n||3);i++){const a=i*2.4+f.x*7;ctx.fillRect(sx+Math.cos(a)*k*TS*0.5,sy+Math.sin(a)*k*TS*0.5,2,2)}}
    else if(f.k==='blood'){ctx.fillStyle=`rgba(120,15,10,${0.7*(1-k)})`;ctx.beginPath();ctx.arc(sx,sy,TS*(0.12+k*0.25),0,TAU);ctx.fill()}
    else if(f.k==='boom'){const r=(f.r||2.5)*TS*(0.3+k*0.8);const gr=ctx.createRadialGradient(sx,sy,0,sx,sy,r);gr.addColorStop(0,`rgba(255,240,190,${1-k})`);gr.addColorStop(0.4,`rgba(255,140,50,${0.8*(1-k)})`);gr.addColorStop(1,'rgba(80,40,20,0)');ctx.fillStyle=gr;ctx.beginPath();ctx.arc(sx,sy,r,0,TAU);ctx.fill()}}
  for(const s of G.smoke){const [sx,sy]=w2s(s.x,s.y);if(!on(sx,sy,120))continue;const k=s.t/s.life;ctx.fillStyle=s.dark?`rgba(40,36,32,${0.45*(1-k)})`:`rgba(70,66,62,${0.28*(1-k)})`;ctx.beginPath();ctx.arc(sx,sy,s.r*TS,0,TAU);ctx.fill()}
  ctx.fillStyle='rgba(10,16,34,0.18)';ctx.fillRect(0,0,VW,VH);
  ctx.save();ctx.globalCompositeOperation='lighter';
  const light=(x,y,r,col)=>{const [sx,sy]=w2s(x,y);const R=r*TS;if(!on(sx,sy,R))return;const gr=ctx.createRadialGradient(sx,sy,0,sx,sy,R);gr.addColorStop(0,col);gr.addColorStop(1,'rgba(0,0,0,0)');ctx.fillStyle=gr;ctx.fillRect(sx-R,sy-R,R*2,R*2)};
  for(const f of FIRES){const fl=0.75+0.25*Math.sin(tm*7+f.x)*Math.sin(tm*3.3+f.y);light(f.x,f.y,(f.big?4:3)*fl,`rgba(255,120,40,${0.32*fl})`)}
  for(const f of G.fx){if(f.k==='muz')light(f.x,f.y,f.big?4:1.8,'rgba(255,200,120,.35)');if(f.k==='boom')light(f.x,f.y,5,`rgba(255,150,60,${0.6*(1-f.t/f.life)})`);if(f.k==='flare'&&f.t>1)light(f.x,f.y,9,`rgba(90,255,120,${0.22*(1-Math.max(0,(f.t-6)/3))})`)}
  ctx.restore();
  for(const f of FIRES){const [sx,sy]=w2s(f.x,f.y);if(!on(sx,sy,40))continue;for(let i=0;i<5;i++){const a=tm*6+i*1.7+f.x;const r=TS*(0.12+0.1*Math.abs(Math.sin(a)));ctx.fillStyle=i%2?'rgba(255,170,60,.8)':'rgba(255,100,30,.7)';ctx.beginPath();ctx.arc(sx+Math.sin(a*1.3)*TS*0.2,sy+Math.cos(a)*TS*0.15,r,0,TAU);ctx.fill()}}
  if(eye){
    fctx.setTransform(DPR,0,0,DPR,0,0);fctx.globalCompositeOperation='source-over';fctx.clearRect(0,0,VW,VH);fctx.fillStyle='rgba(5,6,10,0.64)';fctx.fillRect(0,0,VW,VH);fctx.globalCompositeOperation='destination-out';
    const [px,py]=w2s(p.x,p.y);const R=VIS*TS;const gr=fctx.createRadialGradient(px,py,R*0.55,px,py,R);gr.addColorStop(0,'rgba(0,0,0,1)');gr.addColorStop(1,'rgba(0,0,0,0)');fctx.fillStyle=gr;
    fctx.beginPath();const N=240;for(let i=0;i<N;i++){const a=i/N*TAU,dx=Math.cos(a),dy=Math.sin(a);let d=0;while(d<VIS){d+=0.14;const xx=p.x+dx*d,yy=p.y+dy*d;if(xx<0||yy<0||xx>=W||yy>=H)break;if(grid[(yy|0)*W+(xx|0)]===WALL){d+=0.4;break}}d=Math.min(d,VIS);const [sx,sy]=w2s(p.x+dx*d,p.y+dy*d);i?fctx.lineTo(sx,sy):fctx.moveTo(sx,sy)}fctx.closePath();fctx.fill();
    ctx.setTransform(1,0,0,1,0,0);ctx.drawImage(fog,0,0);ctx.setTransform(DPR,0,0,DPR,0,0)}
  for(const f of G.fx){if(f.k!=='flare')continue;const k=Math.min(1,f.t/1);const x=f.x0+(f.x-f.x0)*k,y=f.y0+(f.y-f.y0)*k;const [sx,sy]=w2s(x,y);const [ox,oy]=w2s(f.x0,f.y0);
    ctx.strokeStyle=`rgba(140,255,150,${0.5*Math.max(0,1-Math.max(0,f.t-2)/3)})`;ctx.lineWidth=2;ctx.beginPath();ctx.moveTo(ox,oy);ctx.quadraticCurveTo((ox+sx)/2,Math.min(oy,sy)-TS*4,sx,sy);ctx.stroke();
    if(f.t>1){const a=Math.max(0,1-Math.max(0,f.t-6)/3);ctx.fillStyle=`rgba(170,255,170,${a})`;ctx.beginPath();ctx.arc(sx,sy-TS*0.3+Math.sin(tm*5)*2,TS*0.22,0,TAU);ctx.fill();ctx.fillStyle=`rgba(90,255,120,${0.25*a})`;ctx.beginPath();ctx.arc(sx,sy,TS*0.9,0,TAU);ctx.fill()}
    if(on(ox,oy,0)&&f.t<6){ctx.strokeStyle='rgba(140,255,150,.7)';ctx.lineWidth=1.5;ctx.beginPath();ctx.arc(ox,oy,TS*0.6+Math.sin(tm*8)*2,0,TAU);ctx.stroke()}}
  const OM=G.mission;if(playing&&OM&&OM.st==='go'&&OM.obj){const [ox,oy]=w2s(OM.obj.x,OM.obj.y);const pul=0.5+0.5*Math.sin(tm*4);
    ctx.strokeStyle=`rgba(216,170,77,${0.55+0.35*pul})`;ctx.lineWidth=2;ctx.setLineDash([6,5]);ctx.beginPath();ctx.arc(ox,oy,TS*2.8,0,TAU);ctx.stroke();ctx.setLineDash([]);
    ctx.lineWidth=4;ctx.strokeStyle='#d8aa4d';ctx.beginPath();ctx.arc(ox,oy,TS*0.6,-Math.PI/2,-Math.PI/2+TAU*Math.min(1,OM.prog));ctx.stroke();
    ctx.fillStyle='#d8aa4d';ctx.beginPath();ctx.arc(ox,oy,TS*0.14,0,TAU);ctx.fill();
    if(eye&&!on(ox,oy,-30)&&OM.team.includes(me)){const [px,py]=w2s(p.x,p.y);const a=Math.atan2(oy-py,ox-px);const ex=clamp(VW/2+Math.cos(a)*VW,40,VW-40),ey=clamp(VH/2+Math.sin(a)*VH,60,VH-60);
      ctx.save();ctx.translate(ex,ey);ctx.rotate(a);ctx.fillStyle='#d8aa4d';ctx.beginPath();ctx.moveTo(14,0);ctx.lineTo(-8,-9);ctx.lineTo(-8,9);ctx.closePath();ctx.fill();ctx.restore()}}
  ctx.textAlign='center';
  if(playing)for(const u of G.units){if(!u.alive||u.kind==='tank'||!vis(u))continue;const [sx,sy]=w2s(u.x,u.y);if(!on(sx,sy,60))continue;
    if(u.uniform==='sov'&&u!==me){ctx.font=`700 ${Math.max(10,TS*0.3)|0}px "PT Sans", sans-serif`;ctx.lineWidth=3;ctx.strokeStyle='rgba(0,0,0,.8)';const lab=u.revealed?`${u.name} — TRAITOR`:u.isCom&&G.comKnown?`${u.name} — COMMISSAR`:u.name;ctx.strokeText(lab,sx,sy-TS*0.62);ctx.fillStyle=u.revealed?'#ff8a70':'#efe9da';ctx.fillText(lab,sx,sy-TS*0.62);
      const hpw=TS*0.8;if(u.hp<u.maxhp){ctx.fillStyle='rgba(0,0,0,.6)';ctx.fillRect(sx-hpw/2,sy+TS*0.5,hpw,3);ctx.fillStyle='#8db363';ctx.fillRect(sx-hpw/2,sy+TS*0.5,hpw*u.hp/u.maxhp,3)}}
    if(u.bark){ctx.font=`${Math.max(11,TS*0.32)|0}px "PT Sans", sans-serif`;const tw=ctx.measureText(u.bark.t).width+12;const by=sy-TS*(u.uniform==='sov'&&u!==me?1.15:0.75);ctx.fillStyle=u.side==='ger'?'rgba(70,74,66,.92)':'rgba(238,232,216,.92)';rr(ctx,sx-tw/2,by-TS*0.35,tw,TS*0.45,4);ctx.fill();ctx.fillStyle=u.side==='ger'?'#f0f0e8':'#1a1814';ctx.fillText(u.bark.t,sx,by-TS*0.03)}}
  if(G.arrest){const [sx,sy]=w2s(G.arrest.u.x,G.arrest.u.y);ctx.strokeStyle='#d8aa4d';ctx.lineWidth=4;ctx.beginPath();ctx.arc(sx,sy,TS*0.7,-Math.PI/2,-Math.PI/2+TAU*G.arrest.t/1.4);ctx.stroke()}
  if(eye&&state==='play'){const p=me;
    const [px,py]=w2s(p.x,p.y);
    for(const h of G.hitInd){const a=1-h.t/h.life;ctx.strokeStyle=h.friendly?`rgba(255,210,80,${a})`:`rgba(230,50,30,${a})`;ctx.lineWidth=6;ctx.beginPath();ctx.arc(px,py,TS*1.6,h.a-0.35,h.a+0.35);ctx.stroke()}
    if(G.dmgFlash>0){ctx.fillStyle=`rgba(150,10,5,${G.dmgFlash*0.6})`;ctx.fillRect(0,0,VW,VH)}
    if(p.hp<40&&p.alive){const gr=ctx.createRadialGradient(VW/2,VH/2,Math.min(VW,VH)*0.3,VW/2,VH/2,Math.max(VW,VH)*0.7);gr.addColorStop(0,'rgba(120,0,0,0)');gr.addColorStop(1,`rgba(120,0,0,${0.35+0.1*Math.sin(tm*4)})`);ctx.fillStyle=gr;ctx.fillRect(0,0,VW,VH)}
    if(!TOUCH&&MOUSE.in){const w=WPN[p.wpn];const d=dist(p.x,p.y,(MOUSE.x+camX)/TS,(MOUSE.y+camY)/TS);const r=6+w.spread*(p.moving?1.6:1)*d*TS*1.5+G.kick*40;ctx.strokeStyle=p.reloadT>0?'rgba(216,170,77,.9)':'rgba(255,255,255,.9)';ctx.lineWidth=1.5;
      for(let i=0;i<4;i++){const a=i*Math.PI/2;ctx.beginPath();ctx.moveTo(MOUSE.x+Math.cos(a)*r,MOUSE.y+Math.sin(a)*r);ctx.lineTo(MOUSE.x+Math.cos(a)*(r+7),MOUSE.y+Math.sin(a)*(r+7));ctx.stroke()}
      if(p.reloadT>0){ctx.beginPath();ctx.arc(MOUSE.x,MOUSE.y,r+11,-Math.PI/2,-Math.PI/2+TAU*(1-p.reloadT/w.reload));ctx.stroke()}}}}

// ================= HUD =================
let hudT=0;
function hudTick(dt){
  hudT-=dt;if(hudT>0)return;hudT=0.12;const p=G.me;if(!p)return;
  $('waveNum').textContent=G.wave?`Assault ${G.wave} / ${WAVES.length}`:'Before dusk';
  const M=G.mission,onS=M&&M.st==='go';
  if(onS){const mine=M.team.includes(p)&&p.alive;$('waveNum').textContent=`Sortie ${M.i+1}: ${M.def.name}`;$('waveState').textContent=`${Math.ceil(Math.max(0,M.tLeft))} s`;
    $('waveSub').textContent=(M.contested?'Germans at the objective — clear them out. ':M.prog>0?'Work under way. ':'')+(mine?(p.isSpy&&!M.sabBy.includes(p)?'Hold X at the objective to sabotage it.':'Hold the yellow marker.'):`Team: ${M.team.map(u=>u.name).join(', ')}.`)}
  else if(G.council){$('waveState').textContent='sortie council';$('waveSub').textContent='The squad is choosing a sortie team.'}
  else if(G.phase==='lull'){const pre=G.mi===G.wave&&G.mi<SORTIES.length;$('waveState').textContent=pre?'sortie council':`next in ${Math.ceil(G.phaseT)} s`;$('waveSub').textContent=pre?'The squad is about to choose a sortie team.':G.wave===0?'Get to a firing position. Ammo crates are in the dugout and the east rooms.':p.isSpy?'Lull. The commissar is going over the evidence.':'Lull. Restock, inspect the fallen, question the squad.'}
  else{const left=G.units.filter(u=>u.alive&&u.side==='ger').length+G.spawnQ.length;$('waveState').textContent=`${left} Germans left`;$('waveSub').textContent=WAVES[G.wave-1].txt}
  $('objWrap').hidden=!onS;if(onS)$('objBar').firstElementChild.style.width=Math.min(100,M.prog*100)+'%';
  const th=trackHTML(G.council?G.council.i:M&&M.st!=='done'?M.i:G.mi);if($('hudTrack').innerHTML!==th)$('hudTrack').innerHTML=th;
  const ov=$('overrun');if(G.overrun>0.3){ov.hidden=false;ov.textContent=`Germans in the command dugout! ${Math.max(0,8-G.overrun).toFixed(1)} s`}else ov.hidden=true;
  const w=WPN[p.wpn];$('wName').textContent=p.alive?w.name:p.escaped?'Escaped':p.arrested?'Arrested':'Killed';$('wCal').textContent=p.alive?w.cal:'';
  $('ammo').innerHTML=p.alive?`${p.reloadT>0?'—':p.mag} <small>/ ${p.reserve}</small>`:'<small>spectating</small>';
  $('extra').innerHTML=!p.alive?'':`Grenades <b>${p.grenades}</b>`+(p.isSpy?` · Flares <b>${p.flares}</b>`:p.isCom?` · Arrests <b>${p.arrestsLeft}</b>`:'');
  const hb=$('meHp').firstElementChild;hb.style.width=Math.max(0,p.hp)+'%';hb.style.background=p.hp<40?'var(--red)':'var(--ok)';
  if(p.isSpy){$('susWrap').hidden=false;$('susLab').textContent='Suspicion on you';const v=G.susp[p.id]||0;$('susMeter').firstElementChild.style.width=Math.min(100,v/80*100)+'%';$('susTxt').textContent=v>=80?'arrest likely':v>=40?'watched':'low'}
  else if(p.isCom){$('susWrap').hidden=false;$('susLab').textContent='Your cover as commissar';const v=G.comGuess[p.id]||0;$('susMeter').firstElementChild.style.width=Math.min(100,v/55*100)+'%';$('susTxt').textContent=G.comKnown||v>=55?'blown — watch your back':v>=30?'thin':'intact'}
  else $('susWrap').hidden=true;
  let html='';
  for(const u of G.people){const st=u.escaped?'<span class="st tr">escaped</span>':u.revealed&&u.alive?'<span class="st tr">TRAITOR</span>':u.arrested?'<span class="st arr">arrested</span>':!u.alive?'<span class="st kia">KIA</span>':`<div class="hpb"><i style="width:${Math.max(0,u.hp/u.maxhp*100)}%"></i></div>`;
    const ww=WPN[u.isPlayer?'ppsh':u.wpn];
    html+=`<tr><td><span class="sw" style="background:${u.col}"></span></td><td>${esc(u.name)}${u===p?' (you)':u.isPlayer?' ●':''}${u.isCom&&(G.comKnown||u===p)?' ★':''}${u.isPlayer&&u.away?' <span class="st arr">away</span>':''}</td><td class="cal">${ww.cal}</td><td>${st}</td>${p.isSpy?`<td><div class="sus" title="suspicion"><i style="width:${Math.min(100,(G.susp[u.id]||0)/80*100)}%"></i></div></td>`:''}</tr>`}
  if($('squadTbl').innerHTML!==html)$('squadTbl').innerHTML=html;$('squadHead').textContent=p.isSpy?'calibre · suspicion':'calibre';
  const pr=[];if(p.alive&&!p.revealed&&!G.council){const it=nearestInteract(p);if(it)pr.push(`<span><kbd>E</kbd> ${esc(it.label)}</span>`);
    if(!p.isSpy){const c=nearestComrade(p,2.6);if(c)pr.push(`<span><kbd>T</kbd> Question ${esc(c.name)}</span>`);
      const ar=p.isCom&&p.arrestsLeft>0?nearestArrestable(p,1.9):null;if(ar)pr.push(`<span><kbd>F</kbd> hold: arrest ${esc(ar.name)} (${p.arrestsLeft} left)</span>`)}
    else if(G.phase==='wave'&&p.flares>0)pr.push('<span><kbd>Q</kbd> Fire green flare at cursor</span>');
    if(p.isSpy&&onS&&M.team.includes(p)&&!M.sabBy.includes(p)&&dist(p.x,p.y,M.obj.x,M.obj.y)<2.8)pr.push('<span><kbd>X</kbd> hold: sabotage the charges</span>')}
  else if(p.alive&&p.revealed)pr.push('<span>Run west to the German lines</span>');
  const ph=pr.join('');if($('prompt').innerHTML!==ph)$('prompt').innerHTML=ph;
  const now=performance.now();if(G.log.some(l=>now-l.at>9000)){G.log=G.log.filter(l=>now-l.at<=9000);renderRadio()}}
function rosterHTML(withStatus){const p=G.me;let h='<tr><th></th><th>Soldier</th><th>Weapon</th><th>Calibre</th>'+(withStatus?'<th>Status</th>':'')+'</tr>';
  for(const u of G.people){const w=WPN[u.isPlayer?'ppsh':u.wpn];const st=u.escaped?'escaped':u.revealed?'unmasked':u.arrested?'arrested':u.alive?'alive':'killed';
    h+=`<tr><td><span class="sw" style="background:${u.col}"></span></td><td>${esc(u.rank)} ${esc(u.name)}${u===p?' (you)':u.isPlayer?' <small style="color:var(--dim)">player</small>':''}</td><td>${w.name}</td><td class="cal">${w.cal}</td>${withStatus?`<td>${st}${withStatus==='end'&&u.isSpy?' · <b style="color:#ff8a70">SPY</b>':''}${u.isCom&&(withStatus==='end'||G.comKnown||u===p)?' · <b style="color:#d8aa4d">COMMISSAR</b>':''}</td>`:''}</tr>`}return h}
function openNotebook(){if(state!=='play'||!G.me)return;state='notebook';$('notebook').hidden=false;$('noteBtn').classList.remove('flash');const me=G.me;
  $('nbEb').textContent=me.isSpy?'Your field notes':me.isCom?'Commissar\'s notebook':'Your notebook';
  $('notes').innerHTML=me.notes.length?[...me.notes].reverse().map(n=>`<div class="note ${n.k}"><time>${n.when}</time>${esc(n.t)}</div>`).join(''):`<p class="empty">${me.isSpy?'The commissar gathers evidence after each assault. Watch the radio log and the suspicion bars.':'Nothing yet. When a comrade falls, find the body and press E to inspect it. Press T next to a comrade to question them.'}</p>`;
  $('nbRoster').innerHTML=rosterHTML(true);
  $('nbHint').textContent=me.isSpy?'German calibres (9×19 mm, 7.92×57 mm) can\'t be traced to you, but a wound from behind still draws attention.':'A wound from behind with a Soviet calibre narrows it to whoever carries that weapon. The spy may also use a captured German MP 40 (9×19 mm).'}
function closeNotebook(){if(state!=='notebook')return;$('notebook').hidden=true;state='play'}

// ================= sortie council screen (display + input events only) =================
let CSEL=null,CKEY='',CVOTE=null;
function councilUI(){
  const C=G&&G.council,el=$('council');
  if(!C||G.over||state==='title'||state==='brief'||!G.me){if(!el.hidden)el.hidden=true;CSEL=null;CKEY='';CVOTE=null;return}
  if(el.hidden){el.hidden=false;sfx('page')}
  const me=G.me,R=roster(),canAct=me.alive&&R.includes(me);const leadMe=C.stage==='pick'&&C.lead===me&&canAct;
  const pk=C.hist.length+':'+C.tries+':'+C.lead.id;if(leadMe&&(!CSEL||CSEL.key!==pk))CSEL={key:pk,set:new Set([me.id]),sent:false};
  const voted=C.votes[me.id]!==undefined||CVOTE===pk;
  const waitOn=R.filter(u=>u.isPlayer&&C.votes[u.id]===undefined).map(u=>u.name);
  const key=[C.stage,pk,C.team.map(u=>u.id).join(','),voted,Math.ceil(Math.max(0,C.t)),CSEL&&[...CSEL.set].join(',')+CSEL.sent,waitOn.join(',')].join('|');
  if(key===CKEY)return;CKEY=key;
  $('cEb').textContent=`Sortie ${C.i+1} of ${SORTIES.length} · team of ${C.k} · ${G.fails} failed so far`;$('cTitle').textContent=C.def.name;$('cTrack').innerHTML=trackHTML(C.i);
  $('cText').innerHTML=`${esc(C.def.brief)} <span style="color:var(--dim)">Success thins the next assault. Failure strengthens it — and three failed sorties hand the block to the Germans.</span>`+
    (me.isSpy?' <b style="color:var(--feld)">Get yourself on the team, then hold X at the objective to sabotage it.</b>':'');
  $('cHist').innerHTML=C.hist.map(esc).join('<br>');
  const who=u=>u===me?'You':`${u.rank} ${u.name}`,secs=Math.ceil(Math.max(0,C.t));
  const tm=C.team.map(u=>esc(nm(u))).join(', ');
  if(C.stage==='pick'){
    if(leadMe){const sel=CSEL.set;
      $('cBody').innerHTML=`<p><b>You lead this sortie${C.forced?' — and it goes out without a vote':''}.</b> Pick ${C.k} soldiers, including yourself if you want to go. ✓/✗ marks show earlier sorties each soldier was on. <span style="color:var(--dim)">(${secs} s)</span></p><div class="pick">`+
        R.map(u=>`<button data-id="${u.id}" aria-pressed="${sel.has(u.id)}" ${!sel.has(u.id)&&sel.size>=C.k||CSEL.sent?'disabled':''}><span class="sw" style="background:${u.col}"></span>${esc(nm(u))}<small>${recHTML(u)}</small></button>`).join('')+'</div>';
      $('cBody').querySelectorAll('.pick button').forEach(b=>b.onclick=()=>{const id=+b.dataset.id;sel.has(id)?sel.delete(id):sel.add(id);CKEY=''});
      $('cFoot').innerHTML=CSEL.sent?'<span style="color:var(--dim)">Sent…</span>':`<button class="go" id="cGo" ${sel.size===C.k?'':'disabled style="opacity:.4"'}>Propose this team</button>`;
      if(!CSEL.sent)$('cGo').onclick=()=>{if(sel.size!==C.k)return;CSEL.sent=true;queueEvent(['p',[...sel]]);CKEY=''}}
    else{$('cBody').innerHTML=`<p>${esc(who(C.lead))} ${C.lead===me?'are':'is'} leading and choosing a team of ${C.k}… <span style="color:var(--dim)">(${secs} s)</span></p>`;$('cFoot').innerHTML=''}}
  else if(C.stage==='vote'){
    $('cBody').innerHTML=`<p>${esc(who(C.lead))} ${C.lead===me?'propose':'proposes'}: <b class="team">${tm}</b></p><p>Approve or reject the team. It goes out if a majority approves.${waitOn.length?` <span style="color:var(--dim)">Waiting on ${esc(listNames(waitOn))} (${secs} s).</span>`:''}</p>`;
    if(canAct&&!voted){$('cFoot').innerHTML='<button class="go" id="cY">Approve</button><button class="sub" id="cN">Reject</button>';
      $('cY').onclick=()=>{CVOTE=pk;queueEvent(['v',1]);CKEY=''};$('cN').onclick=()=>{CVOTE=pk;queueEvent(['v',0]);CKEY=''}}
    else $('cFoot').innerHTML=`<span style="color:var(--dim)">${canAct?'Vote cast. ':''}Votes are revealed together.</span>`}
  else if(C.stage==='result'){
    if(C.forced&&!C.voters){$('cBody').innerHTML=`<p>Two teams have been turned down. Battalion orders this one out — no vote: <b class="team">${tm}</b></p>`}
    else{$('cBody').innerHTML=`<p>Team: <b class="team">${tm}</b></p><div class="votes">`+C.voters.map(u=>{const v=C.votes[u.id];return `<div><span class="sw" style="background:${u.col}"></span>${esc(nm(u))}<span class="${v?'y':'n'}">${v?'yes':'no'}</span></div>`}).join('')+
      `</div><p><b style="color:${C.ok?'var(--ok)':'var(--red)'}">${C.ok?'Approved':'Rejected'} ${C.yes}–${C.no}.</b> ${C.ok?'The team moves out.':'Leadership passes to the next soldier.'}</p>`}
    $('cFoot').innerHTML=`<span style="color:var(--dim)">${C.ok?'Moving out':'Next proposal'} in ${secs} s</span>`}}

// ================= screens =================
let ROLE='comrade',DIFFSEL='normal';try{const d=localStorage.getItem('ac_diff');if(DIFF[d])DIFFSEL=d}catch(e){}
function keysHTML(role){return [['WASD','Move'],['Mouse','Aim · left click to fire'],['R','Reload'],['G / right click','Throw grenade'],['1 · 2','Switch weapon'],['E',role==='spy'?'Use: ammo crate, take a German weapon':'Use: ammo crate, inspect a body, take a German weapon'],
  ...(role==='spy'?[['Q','Fire a green flare (calls German mortars)'],['Hold X','Sabotage a sortie (at the objective)']]:role==='com'?[['T','Question the nearest comrade'],['Hold F','Arrest the nearest comrade (2 arrests — reveals you)']]:[['T','Question the nearest comrade']]),['N','Notebook'],['Esc',NET?'Menu':'Pause']].map(([k,v])=>`<kbd>${k}</kbd><span>${v}</span>`).join('')+(TOUCH?'<kbd>Touch</kbd><span>Left stick moves, right stick aims and fires.</span>':'')}
function showBrief(){
  const p=G.me,role=roleOf(p),spy=role==='spy',multi=G.humans.length>1;
  const sortieP='<p><b>Sorties.</b> Before every assault the squad sends a team into no-man\'s land. A rotating leader proposes the team and everyone votes; after two rejections battalion orders the next one out. Out there, the spy can secretly rig the charges — the squad only learns <i>that</i> it was sabotaged, never by whom. A clean sortie thins the next assault; a failed one feeds it. <b>Three failed sorties and the block falls.</b></p>';
  const others=multi?`<p><b>${G.humans.length} players</b> are in this squad${G.squad.length?`, with ${G.squad.length} bots`:''}. Any of them could be the spy or the commissar.</p>`:'';
  $('briefRole').textContent=spy?'Brandenburger':role==='com'?'Commissar':'Soldier';$('briefRole').className=spy?'spy':'com';
  $('briefSub').textContent=spy?'Abwehr special unit, in Red Army uniform':role==='com'?'Secret political officer · five assaults until dawn':'Rifleman · five assaults until dawn';
  $('briefText').innerHTML=(spy?
   `<p>You are ${esc(p.name)}, an Abwehr infiltrator in a Red Army greatcoat. Somewhere in the squad is a <b>secret commissar</b> hunting you. He goes over every body after each assault: a 7.62×25 mm wound in the back points at the PPSh carriers, a captured MP 40 hides the calibre, and a green flare brings German mortars down on the squad.</p>${sortieP}<p><b>You win</b> if three sorties fail, if <b>you kill the commissar</b> (he gives himself away by questioning people and making arrests), or if the command dugout falls. <b>You lose</b> if you are arrested, killed, or the line holds until dawn.</p>`:
   role==='com'?
   `<p>You are Commissar ${esc(p.name)}, wearing a private's coat. Nobody knows what you are — keep it that way. One of the squad is a German infiltrator who shoots comrades in the back, fires green flares for the mortars, and rigs sorties.</p><p><b>Inspect bodies</b>, <b>question the squad</b>, and <b>arrest</b> the spy (two arrests). But if the spy sees you asking questions he will work out who you are — and <b>his other way to win is to kill you</b>. Watch your cover meter. An arrest reveals you to everyone.</p>${sortieP}<p>You lose if you die, if three sorties fail, or the Germans hold the command dugout for eight seconds.</p>`:
   `<p>You are Private ${esc(p.name)}. Somewhere in the squad is a German spy — and a <b>secret commissar</b> hunting him. You don't know who either of them is.</p><p>Hold the line, go out on sorties, and use your votes well: keep anyone who was on a sabotaged sortie off the next team. You can inspect bodies and question comrades too — but the spy can't tell a curious private from the commissar. If you work out who the commissar is, keep them alive — <b>the spy wins if he kills the commissar.</b></p>${sortieP}<p>The squad wins if the line holds until dawn. You lose if you die, three sorties fail, the commissar is assassinated, or the dugout falls.</p>`)+others;
  $('keysList').innerHTML=keysHTML(role);
  $('briefRoster').innerHTML=rosterHTML(false);
  $('briefHint').textContent=spy?'The commissar is one of the others. Watch who asks questions.':'Three calibres on the line: 7.62×25 mm (PPSh), 7.62×54R (rifles and the DP-28), 14.5×114 mm (the PTRD anti-tank rifle).';
  $('briefGo').textContent=NET?'Ready':'Take position';$('briefGo').disabled=false;
  $('brief').hidden=false;state='brief'}
function startPlay(){
  $('brief').hidden=true;$('hud').hidden=false;state='play';G.log=[];renderRadio();const me=G.me;
  document.querySelectorAll('#touch .ask').forEach(b=>b.hidden=me.isSpy);document.querySelectorAll('#touch .cm').forEach(b=>b.hidden=!me.isCom);document.querySelectorAll('#touch .sp').forEach(b=>b.hidden=!me.isSpy);
  $('touch').hidden=!TOUCH;$('banner').hidden=true;$('speech').hidden=true;
  logMsg('Dusk. The Germans will attack soon. Pick a firing position.');
  if(me.isSpy)logMsg('Nobody suspects you yet. Keep it that way.');else if(me.isCom)logMsg('Nobody knows you are the commissar. Keep it that way.')}
// sw: true = the spy's side won, false = the squad won, 'escaped' = single-player spy got away
function endGame(sw,text){if(G.over)return;G.over=true;G.result={sw,text};showEnd()}
function showEnd(){
  const me=G.me;if(!me||state==='title')return;const R=G.result;state='over';
  ['hud','notebook','speech','council','pause','brief'].forEach(i=>$(i).hidden=true);$('away').hidden=true;
  const spy=me.isSpy,escaped=R.sw==='escaped',win=!escaped&&(R.sw===true)===spy;
  const text=typeof R.text==='function'?R.text(me):R.text;
  $('endKicker').textContent=(spy?'Brandenburger':me.isCom?'Commissar':'Soldier')+' — debrief';
  const t=$('endTitle');t.textContent=escaped?'Escaped':win?'Victory':'Defeat';t.className=escaped?'':win?'win':'lose';
  $('endText').textContent=text+(spy?'':` The spy was ${G.spy.name}.`)+(me.isCom?'':` The commissar was ${G.com.name}.`);
  $('endStats').innerHTML=`${G.diff.name} · Assaults reached <b>${G.wave} / ${WAVES.length}</b> · Germans killed <b>${G.kills}</b> (yours <b>${me.kills}</b>) · Comrades lost <b>${G.lost}</b>`+` · Sorties <b>${G.track.filter(x=>x==='ok').length} ✓ ${G.fails} ✗</b>`+(me.isCom?` · Arrests used <b>${2-me.arrestsLeft}</b>`:'');
  $('endRoster').innerHTML=rosterHTML('end');
  $('againBtn').textContent=NET?'Back to the lobby':'Fight again';
  $('end').hidden=false;sfx(win?'win':'lose')}
function toTitle(){['end','pause','brief','notebook','council','lobby'].forEach(i=>$(i).hidden=true);$('away').hidden=true;$('hud').hidden=true;newGame({demo:true,seed:(crnd()*1e9)|0});state='title';$('title').hidden=false}

// ================= audio =================
const SND={ctx:null,master:null,muted:false,noise:null,budget:0};
function audioInit(){if(SND.ctx)return;try{const AC=window.AudioContext||window.webkitAudioContext;SND.ctx=new AC();SND.master=SND.ctx.createGain();SND.master.gain.value=SND.muted?0:0.45;SND.master.connect(SND.ctx.destination);
  const len=SND.ctx.sampleRate*2;const b=SND.ctx.createBuffer(1,len,SND.ctx.sampleRate);const d=b.getChannelData(0);for(let i=0;i<len;i++)d[i]=Math.random()*2-1;SND.noise=b;
  const src=SND.ctx.createBufferSource();src.buffer=b;src.loop=true;const f=SND.ctx.createBiquadFilter();f.type='lowpass';f.frequency.value=300;const gn=SND.ctx.createGain();gn.gain.value=0.05;src.connect(f);f.connect(gn);gn.connect(SND.master);src.start()}catch(e){SND.ctx=null}}
function out(pan){if(pan&&SND.ctx.createStereoPanner){const p=SND.ctx.createStereoPanner();p.pan.value=pan;p.connect(SND.master);return p}return SND.master}
function nb(dur,freq,type,gain,o={}){const c=SND.ctx;const t=c.currentTime+(o.delay||0);const s=c.createBufferSource();s.buffer=SND.noise;const f=c.createBiquadFilter();f.type=type;f.frequency.value=freq;f.Q.value=o.q||0.8;const g=c.createGain();g.gain.setValueAtTime(0.0001,t);g.gain.exponentialRampToValueAtTime(Math.max(0.0002,gain),t+0.004);g.gain.exponentialRampToValueAtTime(0.0001,t+dur);s.connect(f);f.connect(g);g.connect(out(o.pan));s.start(t,Math.random()*1.5);s.stop(t+dur+0.05)}
function tn(fr,dur,type,gain,o={}){const c=SND.ctx;const t=c.currentTime+(o.delay||0);const os=c.createOscillator();os.type=type;os.frequency.setValueAtTime(fr,t);if(o.slide)os.frequency.exponentialRampToValueAtTime(fr*o.slide,t+dur);const g=c.createGain();g.gain.setValueAtTime(0.0001,t);g.gain.exponentialRampToValueAtTime(Math.max(0.0002,gain),t+0.006);g.gain.exponentialRampToValueAtTime(0.0001,t+dur);os.connect(g);g.connect(out(o.pan));os.start(t);os.stop(t+dur+0.05)}
function sfxAt(n,x,y){if(!SND.ctx||SND.muted||state!=='play'||!G.me)return;const d=dist(x,y,G.me.x,G.me.y);const v=1/(1+d/7);if(v<0.06||SND.budget>9)return;SND.budget++;sfx(n,v,clamp((x-G.me.x)/18,-0.9,0.9))}
function sfx(n,v=1,pan=0){if(!SND.ctx||SND.muted)return;try{const o={pan};switch(n){
  case 'smg':nb(0.07,1900,'bandpass',0.45*v,o);tn(150,0.05,'triangle',0.15*v,o);break;
  case 'smg2':nb(0.08,1500,'bandpass',0.4*v,o);tn(130,0.06,'triangle',0.13*v,o);break;
  case 'rifle':nb(0.22,1300,'bandpass',0.75*v,o);tn(85,0.18,'sine',0.4*v,o);break;
  case 'rifle2':nb(0.2,1100,'bandpass',0.65*v,o);tn(75,0.18,'sine',0.35*v,o);break;
  case 'lmg':nb(0.1,1400,'bandpass',0.5*v,o);tn(100,0.08,'sine',0.25*v,o);break;
  case 'mg42':nb(0.05,2300,'bandpass',0.42*v,o);tn(110,0.04,'triangle',0.12*v,o);break;
  case 'ptrd':nb(0.45,800,'bandpass',1.0*v,o);tn(55,0.4,'sine',0.6*v,o);break;
  case 'cannon':nb(0.8,300,'lowpass',1.0*v,o);tn(45,0.6,'sine',0.7*v,o);break;
  case 'boom':nb(1.1,200,'lowpass',0.95*v,o);tn(55,0.6,'sine',0.6*v,{pan,slide:0.5});break;
  case 'boomBig':nb(1.6,150,'lowpass',1.0*v,o);tn(45,0.9,'sine',0.7*v,{pan,slide:0.6});break;
  case 'whistle':tn(1500,1.0,'sine',0.07*v,{pan,slide:0.35});break;
  case 'flare':nb(0.6,2500,'highpass',0.25*v,o);tn(500,0.7,'sine',0.08*v,{pan,slide:2.5});break;
  case 'ric':tn(2600,0.18,'sine',0.06*v,{pan,slide:0.35});break;
  case 'throw':nb(0.15,700,'bandpass',0.15*v,o);break;
  case 'reload':nb(0.05,3000,'bandpass',0.3);nb(0.05,2500,'bandpass',0.3,{delay:0.18});break;
  case 'empty':tn(1800,0.03,'square',0.06);break;
  case 'hurt':nb(0.15,300,'lowpass',0.5);break;
  case 'page':nb(0.12,4000,'highpass',0.12);break;
  case 'alarm':for(let i=0;i<3;i++){tn(880,0.12,'square',0.07,{delay:i*0.25});tn(660,0.12,'square',0.07,{delay:i*0.25+0.12})}break;
  case 'whistleAttack':for(let i=0;i<3;i++)tn(2300,0.18,'sine',0.06,{delay:i*0.25});tn(2300,0.6,'sine',0.06,{delay:0.8});break;
  case 'tankHorn':nb(2.5,90,'lowpass',0.35);break;
  case 'distant':nb(2.2,90,'lowpass',0.4*v);break;
  case 'win':[523,659,784,1047].forEach((f,i)=>tn(f,0.35,'triangle',0.13,{delay:i*0.16}));break;
  case 'lose':[392,330,262,196].forEach((f,i)=>tn(f,0.45,'triangle',0.13,{delay:i*0.22}));break}}catch(e){}}

// ================= input =================
// Keys and clicks never touch the simulation directly: they become this player's input record for an upcoming tick.
const EVQ=[];
function queueEvent(e){EVQ.push(e)}
function cursorWorld(){const p=G.me;if(TOUCH)return[p.x+Math.cos(p.aim)*10,p.y+Math.sin(p.aim)*10];return[(MOUSE.x+camX)/TS,(MOUSE.y+camY)/TS]}
const q100=v=>Math.round(v*100);
function collectInput(){
  if(window.__acBot&&G&&G.me)return window.__acBot(G);// automated tests only
  const p=G&&G.me;const live=!!p&&p.alive&&state==='play'&&!G.council;let mx=0,my=0;
  if(live){if(KEYS.KeyW||KEYS.ArrowUp)my-=1;if(KEYS.KeyS||KEYS.ArrowDown)my+=1;if(KEYS.KeyA||KEYS.ArrowLeft)mx-=1;if(KEYS.KeyD||KEYS.ArrowRight)mx+=1;if(TOUCH){mx+=TCH.mx;my+=TCH.my}}
  let aim=p?p.aim:Math.PI;
  if(live){if(TOUCH){if(TCH.aiming)aim=Math.atan2(TCH.ay,TCH.ax);else if(Math.hypot(mx,my)>0.1)aim=Math.atan2(my,mx)}else if(MOUSE.in)aim=Math.atan2((MOUSE.y+camY)/TS-p.y,(MOUSE.x+camX)/TS-p.x)}
  let b=0;if(live){if(TOUCH?TCH.fire:MOUSE.down)b|=1;if(KEYS.KeyF)b|=2;if(KEYS.KeyX)b|=4}
  const r=[q100(clamp(mx,-1,1)),q100(clamp(my,-1,1)),Math.round(aim*1000),b];const ev=EVQ.splice(0);if(ev.length)r.push(ev);return r}
function press(code){
  if(code==='Escape'){if(state==='notebook')closeNotebook();else if(state==='play'){state='pause';$('pause').hidden=false;$('keysList2').innerHTML=keysHTML(roleOf(G.me))}else if(state==='pause'){state='play';$('pause').hidden=true}return}
  if(code==='KeyN'){if(state==='notebook')closeNotebook();else openNotebook();return}
  if(state!=='play'||!G.me||!G.me.alive||G.council)return;
  switch(code){case 'KeyR':queueEvent(['r']);break;case 'KeyE':queueEvent(['e']);break;case 'KeyG':{const [x,y]=cursorWorld();queueEvent(['g',q100(x),q100(y)]);break}case 'KeyT':queueEvent(['t']);break;case 'KeyF':queueEvent(['f']);break;
    case 'KeyQ':{const [x,y]=G.me&&TOUCH?[G.me.x+Math.cos(G.me.aim)*12,G.me.y+Math.sin(G.me.aim)*12]:cursorWorld();queueEvent(['q',q100(x),q100(y)]);break}case 'Digit1':queueEvent(['s',0]);break;case 'Digit2':queueEvent(['s',-1]);break}}
window.addEventListener('keydown',e=>{if(e.target.tagName==='INPUT')return;if(['Space','ArrowUp','ArrowDown','ArrowLeft','ArrowRight'].includes(e.code))e.preventDefault();if(!KEYS[e.code])press(e.code);KEYS[e.code]=true});
window.addEventListener('keyup',e=>{KEYS[e.code]=false});
window.addEventListener('blur',()=>{for(const k in KEYS)KEYS[k]=false;MOUSE.down=false});
cv.addEventListener('mousemove',e=>{const r=cv.getBoundingClientRect();MOUSE.x=e.clientX-r.left;MOUSE.y=e.clientY-r.top;MOUSE.in=true});
cv.addEventListener('mouseleave',()=>{MOUSE.in=false});
cv.addEventListener('mousedown',e=>{if(TOUCH)return;audioInit();if(e.button===0)MOUSE.down=true;else if(e.button===2)press('KeyG')});
window.addEventListener('mouseup',e=>{if(e.button===0)MOUSE.down=false});
cv.addEventListener('contextmenu',e=>e.preventDefault());
function stick(el,cb,end){let id=null;const k=el.querySelector('i');
  const mv=e=>{if(e.pointerId!==id)return;const r=el.getBoundingClientRect();let dx=(e.clientX-r.left-r.width/2)/(r.width/2),dy=(e.clientY-r.top-r.height/2)/(r.height/2);const l=Math.hypot(dx,dy);if(l>1){dx/=l;dy/=l}k.style.transform=`translate(${dx*36}px,${dy*36}px)`;cb(dx,dy)};
  el.addEventListener('pointerdown',e=>{audioInit();id=e.pointerId;el.setPointerCapture(id);mv(e)});
  el.addEventListener('pointermove',mv);const up=e=>{if(e.pointerId!==id)return;id=null;k.style.transform='';end()};el.addEventListener('pointerup',up);el.addEventListener('pointercancel',up)}
stick($('stickL'),(x,y)=>{TCH.mx=x;TCH.my=y},()=>{TCH.mx=0;TCH.my=0});
stick($('stickR'),(x,y)=>{TCH.ax=x;TCH.ay=y;TCH.aiming=Math.hypot(x,y)>0.2;TCH.fire=Math.hypot(x,y)>0.55},()=>{TCH.aiming=false;TCH.fire=false});
document.querySelectorAll('#touch .tbtns button').forEach(b=>{b.addEventListener('pointerdown',e=>{e.preventDefault();audioInit();KEYS[b.dataset.k]=true;press(b.dataset.k)});const up=()=>{KEYS[b.dataset.k]=false};b.addEventListener('pointerup',up);b.addEventListener('pointercancel',up);b.addEventListener('pointerleave',up)});

// ================= single player loop =================
let RALPHA=1,lastStepAt=0;
function doStep(inputs){step(inputs);lastStepAt=performance.now()}
const Solo={acc:0,pump(dt){if(NET||state!=='play'||!G||G.over){this.acc=0;return}this.acc+=dt;let n=0;while(this.acc>=DT&&n<6){this.acc-=DT;n++;doStep([collectInput()])}if(n>=6)this.acc=0}};
// draw units and bullets part-way between the last two ticks, so a 30 Hz simulation looks smooth at any frame rate
function withLerp(fn){const a=RALPHA;if(!G||a>=1){fn();return}const sv=[];
  for(const L of [G.units,G.proj])for(const u of L)if(u.ox!==undefined){sv.push(u,u.x,u.y);u.x=u.ox+(u.x-u.ox)*a;u.y=u.oy+(u.y-u.oy)*a}
  try{fn()}finally{for(let i=0;i<sv.length;i+=3){sv[i].x=sv[i+1];sv[i].y=sv[i+2]}}}

// ================= snapshots & state hash =================
// A snapshot is the whole simulation (with shared references and cycles kept) as JSON. It repairs a peer that has
// drifted out of sync, brings a reloaded tab back into the game, and lets a reloaded host recover from a client.
const SNAP_SKIP=new Set(['fx','smoke','hitInd','dmgFlash','shake','kick','banner','log','bark','fireT','ambT','ox','oy','me','result']);
function serialize(){
  const ids=new Map(),nodes=[];
  const enc=v=>{if(v===null||typeof v!=='object'){if(typeof v==='number'&&!isFinite(v))return{$n:String(v)};return v}
    let id=ids.get(v);if(id!==undefined)return{$r:id};id=nodes.length;ids.set(v,id);nodes.push(null);let o;
    if(Array.isArray(v))o={a:v.map(enc)};else if(ArrayBuffer.isView(v))o={u8:Array.from(v)};
    else{const m={};for(const k in v){if(SNAP_SKIP.has(k))continue;const x=v[k];if(typeof x==='function'||x===undefined)continue;m[k]=enc(x)}o={o:m}}
    nodes[id]=o;return{$r:id}};
  const root=enc({G,grid,ck,FIRES,CSPOTS,RS,UID});return JSON.stringify({v:1,root,nodes})}
function applySnapshot(str,seat){
  const {root,nodes}=JSON.parse(str);const objs=nodes.map(n=>n.a?[]:n.u8?new Uint8Array(n.u8):{});
  const dec=v=>{if(v===null||typeof v!=='object')return v;if(v.$n!==undefined)return Number(v.$n);return objs[v.$r]};
  nodes.forEach((n,i)=>{const t=objs[i];if(n.a){for(const x of n.a)t.push(dec(x))}else if(n.o){for(const k in n.o)t[k]=dec(n.o[k])}});
  const S=dec(root);G=S.G;grid.set(S.grid);ck.set(S.ck);FIRES.length=0;FIRES.push(...S.FIRES);CSPOTS.length=0;CSPOTS.push(...S.CSPOTS);RS=S.RS;UID=S.UID;
  G.fx=[];G.smoke=[];G.hitInd=[];G.dmgFlash=0;G.shake=0;G.kick=0;G.banner=null;G.log=[];G.me=G.humans[seat]||null;$('banner').hidden=true}
const HB=new Float64Array(1),HU=new Uint32Array(HB.buffer);
function stateHash(){let h=2166136261>>>0;const mix=x=>{h=Math.imul(h^(x>>>0),16777619)>>>0};const f=v=>{HB[0]=v||0;mix(HU[0]);mix(HU[1])};
  mix(G.tick);mix(RS);mix(G.units.length);mix(G.proj.length);mix(G.wave);mix(G.fails);mix(G.sched.length);
  for(const u of G.units){mix(u.id);mix(u.alive?1:0);f(u.x);f(u.y);f(u.hp);f(u.aim)}for(const p of G.proj){f(p.x);f(p.y)}return h}
async function packStr(str){
  if(typeof CompressionStream==='undefined')return{z:0,s:str};
  const buf=new Uint8Array(await new Response(new Blob([str]).stream().pipeThrough(new CompressionStream('gzip'))).arrayBuffer());
  let bin='';for(let i=0;i<buf.length;i+=0x8000)bin+=String.fromCharCode.apply(null,buf.subarray(i,i+0x8000));return{z:1,s:btoa(bin)}}
async function unpackStr(z,s){if(!z)return s;const bin=atob(s);const u=new Uint8Array(bin.length);for(let i=0;i<bin.length;i++)u[i]=bin.charCodeAt(i);
  return await new Response(new Blob([u]).stream().pipeThrough(new DecompressionStream('gzip'))).text()}

// ================= lockstep =================
// Every peer sends only its own input for tick t+delay. The host gathers one input from every player per tick and
// sends the bundle to everyone; each peer runs a tick only once its bundle arrives. Bots need no syncing — every
// peer runs the same bot code with the same seed on the same inputs. If any player's input is missing (tab in the
// background, connection lost) the bundle waits, so the whole room pauses until that player is back.
const HHIST=new Map();
class Lock{
  constructor(room,exec){this.room=room;this.exec=exec;this.nextIn=exec+1;this.acc=0;this.bundles=new Map();this.hist=new Map();this.stallT=0}
  pump(dt){
    if(!G||G.over)return;
    this.acc=Math.min(this.acc+dt,0.25);
    while(this.acc>=DT&&this.nextIn<=this.exec+this.room.delay){this.acc-=DT;const t=this.nextIn++;this.room.sendInput(t,collectInput())}
    if(this.nextIn>this.exec+this.room.delay)this.acc=Math.min(this.acc,DT);
    let n=0;const lag=this.bundles.size;
    while(this.bundles.has(this.exec+1)&&n<(lag>3?24:2)){const t=++this.exec;const b=this.bundles.get(t);this.bundles.delete(t);this.hist.set(t,b);this.hist.delete(t-300);doStep(b);n++;
      if(t%30===0){const h=stateHash();HHIST.set(t,h);HHIST.delete(t-3000);this.room.tickHash(t,h)}if(G.over)break}
    this.stallT=n||this.bundles.has(this.exec+1)?0:this.stallT+dt}
  add(t,d){if(t>this.exec)this.bundles.set(t,d)}
  // after loading a snapshot taken at tick T: rewind to T and replay any bundles already received for later ticks
  rewind(T){for(const [t,b] of this.hist)if(t>T)this.bundles.set(t,b);this.hist.clear();for(const t of [...this.bundles.keys()])if(t<=T)this.bundles.delete(t);this.exec=T;this.nextIn=T+1;lastStepAt=performance.now()}}
// (inputs after T are sent again: the host keeps the first copy it got for a tick, and a reloaded host has none)

// ================= peer-to-peer rooms (PeerJS) =================
const PREFIX='among-comrades-v1-',CODE_CHARS='ABCDEFGHJKLMNPQRSTUVWXYZ23456789',MAXH=8,CHUNK=12000;// PeerJS's JSON channel drops any message of 16,300 bytes or more
const genCode=()=>{let c='';for(let i=0;i<5;i++)c+=CODE_CHARS[NM.floor(crnd()*CODE_CHARS.length)];return c};
const genTok=()=>crnd().toString(36).slice(2)+crnd().toString(36).slice(2);
const store={get(k){try{return JSON.parse(localStorage.getItem(k))}catch(e){return null}},set(k,v){try{localStorage.setItem(k,JSON.stringify(v))}catch(e){}},del(k){try{localStorage.removeItem(k)}catch(e){}}};
let NET=null;
// Signalling broker: PeerJS's free public server by default. `?peer=host:port` (or window.AC_PEER) points at a
// self-hosted one instead — only the initial handshake goes through it; gameplay traffic is direct between browsers.
function peerOpts(){const o={debug:0};const q=new URLSearchParams(location.search).get('peer');const w=window.AC_PEER;
  if(w)Object.assign(o,w);else if(q){const [h,pt]=q.split(':');Object.assign(o,{host:h,port:+pt||443,path:'/',secure:!/^(localhost|127\.)/.test(h)})}return o}
class Room{
  constructor(name){this.name=name;this.peer=null;this.isHost=false;this.code='';this.seat=-1;this.seats=[];this.host=null;this.started=false;this.go=false;this.lock=null;this.cfg=null;
    this.delay=4;this.wait=[];this.snapIn=new Map();this.hostLost=false;this.ready=new Set();this.IN=new Map();this.nextB=1;this.hostH=new Map();this.peerH=new Map();this.snapping=new Set();this.away=false;this.desyncs=0;this.recovering=false;this.timers=[];this.closed=false}
  static ok(){return typeof Peer!=='undefined'&&typeof RTCPeerConnection!=='undefined'}
  // ---------- host ----------
  hostNew(cb){this.isHost=true;this.code=genCode();this.seat=0;this.token=genTok();this.seats=[{name:this.name,token:this.token,conn:null,connected:true,away:false,rtt:0}];this.diff=DIFFSEL;this.openHost(cb)}
  hostRecover(rec,cb){this.isHost=true;this.recovering=true;this.code=rec.code;this.seat=0;this.token=rec.token;this.cfg=rec.cfg;this.delay=rec.cfg.delay;this.started=true;this.go=true;
    this.seats=rec.cfg.names.map((n,i)=>({name:n,token:rec.tokens[i],conn:null,connected:i===0,away:false,rtt:0}));this.openHost(cb)}
  openHost(cb,tries=0){
    let peer;try{peer=new Peer(PREFIX+this.code,peerOpts())}catch(e){cb(e);return}this.peer=peer;let opened=false;
    peer.on('open',()=>{opened=true;cb(null);this.timers.push(setInterval(()=>this.hostPulse(),500))});
    peer.on('error',e=>{if(e.type==='unavailable-id'&&!opened){try{peer.destroy()}catch(_){}
        if(this.recovering&&tries<20){setTimeout(()=>this.openHost(cb,tries+1),2500);return}if(!this.started){this.code=genCode();this.openHost(cb,tries+1);return}}
      if(!opened)cb(e)});
    peer.on('connection',c=>{c.on('data',m=>this.hostData(c,m));c.on('close',()=>this.hostClose(c));c.on('error',e=>console.warn('connection error',e&&e.type))});
    peer.on('disconnected',()=>{if(!this.closed)try{peer.reconnect()}catch(_){}})}
  seatOf(c){return this.seats.findIndex(s=>s.conn===c)}
  sendTo(i,m){const s=this.seats[i];if(s&&s.conn&&s.connected)try{s.conn.send(m)}catch(e){}}
  bcast(m){for(let i=1;i<this.seats.length;i++)this.sendTo(i,m)}
  lobbyMsg(){return{t:'lobby',code:this.code,diff:this.diff,seats:this.seats.map(s=>({name:s.name,connected:s.connected,rtt:s.rtt}))}}
  pushLobby(){this.bcast(this.lobbyMsg());lobbyUI()}
  hostData(c,m){if(!m||typeof m!=='object')return;let i=this.seatOf(c);
    switch(m.t){
      case 'hello':{const tok=String(m.token||''),name=String(m.name||'Comrade').slice(0,12);let k=this.seats.findIndex(s=>s.token===tok);
        if(!this.started){if(k<0){if(this.seats.length>=MAXH){try{c.send({t:'full'})}catch(e){}return}this.seats.push({name,token:tok,conn:c,connected:true,away:false,rtt:0});k=this.seats.length-1}
          else Object.assign(this.seats[k],{conn:c,connected:true,name});try{c.send({t:'welcome',seat:k,code:this.code})}catch(e){}this.pushLobby();return}
        if(k<1){try{c.send({t:'reject',why:'That battle has already started.'})}catch(e){}return}
        Object.assign(this.seats[k],{conn:c,connected:true,away:false});
        if(this.recovering&&!this.lock){try{c.send({t:'needsnap'})}catch(e){}return}
        this.sendTo(k,{t:'start',cfg:this.cfg,seat:k,resume:true});this.snapTo([k]);return}
      case 'i':if(i>0)this.recvInput(i,m.k|0,m.d);return;
      case 'h':if(i>0){let mm=this.peerH.get(m.k);if(!mm)this.peerH.set(m.k,mm=new Map());mm.set(i,m.h);this.checkHash(m.k)}return;
      case 'away':if(i>0){this.seats[i].away=!!m.v}return;
      case 'ready':if(i>0){this.ready.add(i);this.checkGo()}return;
      case 'pong':if(i>0){this.seats[i].rtt=Math.round(performance.now()-m.ts);lobbyUI()}return;
      case 'snap':this.snapPart(m,str=>this.recoverFrom(str,m.k,i));return}}
  hostClose(c){const i=this.seatOf(c);if(i<0)return;this.seats[i].connected=false;this.seats[i].conn=null;
    if(!this.started){this.seats.splice(i,1);for(let k=1;k<this.seats.length;k++)this.sendTo(k,{t:'welcome',seat:k,code:this.code});this.pushLobby()}}
  hostPulse(){
    if(!this.started){for(let i=1;i<this.seats.length;i++)this.sendTo(i,{t:'ping',ts:performance.now()});return}
    const w=this.lock?this.waitingOn():[];this.wait=w;this.bcast({t:'wait',w})}
  waitingOn(){const m=this.IN.get(this.nextB)||[];const out=[];
    for(let i=0;i<this.seats.length;i++){if(m[i]!==undefined)continue;const s=this.seats[i];const away=i===0?this.away:s.away;
      out.push(`${s.name} (${!s.connected?'disconnected — waiting for them to rejoin':away?'away — tab in the background':'connection is slow'})`)}return out}
  setDiff(d){this.diff=d;this.pushLobby()}
  startGame(){
    if(this.started)return;const maxRtt=Math.max(0,...this.seats.map(s=>s.rtt||0));
    this.delay=clamp(Math.ceil((maxRtt*1.25+30)/(DT*1000))+1,3,12);
    this.cfg={seed:(crnd()*0x7fffffff)|0,diff:this.diff,names:this.seats.map(s=>s.name),delay:this.delay};this.started=true;
    store.set('ac_host_'+this.code,{code:this.code,token:this.token,cfg:this.cfg,tokens:this.seats.map(s=>s.token),at:Date.now()});
    for(let i=1;i<this.seats.length;i++)this.sendTo(i,{t:'start',cfg:this.cfg,seat:i});
    this.beginGame(false)}
  checkGo(){if(this.go||!this.started)return;for(let i=0;i<this.seats.length;i++)if(!this.ready.has(i))return;this.go=true;this.bcast({t:'go'});this.launch()}
  recvInput(i,t,d){if(t<this.nextB)return;let m=this.IN.get(t);if(!m)this.IN.set(t,m=new Array(this.seats.length).fill(undefined));if(m[i]===undefined)m[i]=d;this.tryBundle()}
  tryBundle(){if(!this.lock)return;for(;;){const m=this.IN.get(this.nextB);if(!m)return;for(let i=0;i<this.seats.length;i++)if(m[i]===undefined)return;
    this.IN.delete(this.nextB);this.bcast({t:'b',k:this.nextB,d:m});this.lock.add(this.nextB,m);this.nextB++}}
  checkHash(k){const hh=this.hostH.get(k),mm=this.peerH.get(k);if(hh===undefined||!mm)return;
    for(const [i,h] of mm)if(h!==hh){this.desyncs++;console.warn(`desync with ${this.seats[i].name} at tick ${k}; sending a snapshot`);this.snapTo([i])}
    this.peerH.delete(k);for(const kk of this.hostH.keys())if(kk<k-600)this.hostH.delete(kk)}
  async snapTo(list){list=list.filter(i=>!this.snapping.has(i));if(!list.length||!G)return;list.forEach(i=>this.snapping.add(i));
    const k=this.lock?this.lock.exec:G.tick;let str,pk;try{str=serialize();pk=await packStr(str)}catch(e){console.warn('snap build failed',e&&e.stack);list.forEach(i=>this.snapping.delete(i));return}const id=genTok();const n=Math.ceil(pk.s.length/CHUNK)||1;
    for(let j=0;j<n;j++)for(const i of list)this.sendTo(i,{t:'snap',id,k,j,n,z:pk.z,s:pk.s.slice(j*CHUNK,(j+1)*CHUNK)});
    setTimeout(()=>list.forEach(i=>this.snapping.delete(i)),3000)}
  // the host reloaded: rebuild the game from the first returning player's copy, then bring everyone onto it
  recoverFrom(str,k,i){if(this.lock)return;
    newGame({seed:this.cfg.seed,diff:this.cfg.diff,humans:this.cfg.names.map(n=>({name:n}))});applySnapshot(str,0);
    this.lock=new Lock(this,k);this.nextB=k+1;this.IN.clear();this.recovering=false;$('title').hidden=true;$('lobby').hidden=true;startPlay();
    const others=[];for(let j=1;j<this.seats.length;j++)if(this.seats[j].connected&&j!==i){this.sendTo(j,{t:'start',cfg:this.cfg,seat:j,resume:true});others.push(j)}
    this.sendTo(i,{t:'start',cfg:this.cfg,seat:i,resume:true});this.snapTo([i,...others]);logMsg('Back in command. The battle resumes.','good')}
  // ---------- client ----------
  join(code,cb){this.code=code.toUpperCase();const tk='ac_tok_'+this.code;this.token=store.get(tk)||genTok();store.set(tk,this.token);
    let peer;try{peer=new Peer(peerOpts())}catch(e){cb(e);return}this.peer=peer;this.joinCb=cb;
    peer.on('open',()=>this.connectHost());
    peer.on('error',e=>{if(e.type==='peer-unavailable'){if(this.started){this.hostLost=true;return}const f=this.joinCb;this.joinCb=null;f&&f(new Error('Room not found. Check the code.'))}else if(this.joinCb&&!this.host){const f=this.joinCb;this.joinCb=null;f(e)}});
    peer.on('disconnected',()=>{if(!this.closed)try{peer.reconnect()}catch(_){}});
    this.timers.push(setInterval(()=>{if(this.closed||!this.started)return;if(!this.hostLost&&performance.now()-this.lastMsg>4000){this.hostLost=true;try{this.host&&this.host.close()}catch(e){}this.host=null}if(this.hostLost)this.connectHost()},3000))}
  connectHost(){if(this.closed)return;const c=this.peer.connect(PREFIX+this.code,{reliable:true,serialization:'json'});
    c.on('open',()=>{this.host=c;this.hostLost=false;this.lastMsg=performance.now();c.send({t:'hello',name:this.name,token:this.token});if(document.hidden)c.send({t:'away',v:true})});
    c.on('data',m=>this.clientData(m));c.on('close',()=>{if(this.host===c){this.host=null;this.hostLost=true}});c.on('error',()=>{});
    setTimeout(()=>{if(this.joinCb&&!this.host&&!this.started){const f=this.joinCb;this.joinCb=null;f(new Error('No answer from that room code. Check the code and that the host is still there.'))}},12000)}
  send(m){if(this.host)try{this.host.send(m)}catch(e){}}
  clientData(m){if(!m||typeof m!=='object')return;this.lastMsg=performance.now();
    switch(m.t){
      case 'welcome':this.seat=m.seat;if(this.joinCb){const f=this.joinCb;this.joinCb=null;f(null)}lobbyUI();return;
      case 'lobby':this.lobby=m;this.diff=m.diff;lobbyUI();return;
      case 'full':case 'reject':{const f=this.joinCb;this.joinCb=null;const err=new Error(m.why||'That room is full.');if(f)f(err);else{leaveRoom();$('mpMsg').textContent=err.message}return}
      case 'ping':this.send({t:'pong',ts:m.ts});return;
      case 'start':this.joinCb=null;this.cfg=m.cfg;this.seat=m.seat;this.delay=m.cfg.delay;this.started=true;
        if(m.resume){if(this.lock&&G)return;newGame({seed:m.cfg.seed,diff:m.cfg.diff,humans:m.cfg.names.map(n=>({name:n}))});G.me=G.humans[this.seat];this.go=true;this.resuming=true;$('title').hidden=true;$('lobby').hidden=true;$('brief').hidden=true}
        else this.beginGame(false);return;
      case 'go':this.go=true;this.launch();return;
      case 'b':if(this.lock)this.lock.add(m.k,m.d);else(this.early=this.early||[]).push(m);return;
      case 'wait':this.wait=m.w||[];return;
      case 'needsnap':if(G&&this.lock){const k=this.lock.exec,str=serialize();packStr(str).then(pk=>{const id=genTok(),n=Math.ceil(pk.s.length/CHUNK)||1;for(let j=0;j<n;j++)this.send({t:'snap',id,k,j,n,z:pk.z,s:pk.s.slice(j*CHUNK,(j+1)*CHUNK)})})}return;
      case 'snap':this.snapPart(m,str=>this.loadSnap(str,m.k));return}}
  loadSnap(str,k){applySnapshot(str,this.seat);
    if(!this.lock){this.lock=new Lock(this,k);for(const b of this.early||[])this.lock.add(b.k,b.d);this.early=null}else this.lock.rewind(k);
    if(this.resuming){this.resuming=false;startPlay();logMsg('Back with the squad.','good')}}
  // ---------- both ----------
  snapPart(m,done){let e=this.snapIn.get(m.id);if(!e)this.snapIn.set(m.id,e={n:m.n,parts:[],got:0});if(e.parts[m.j]===undefined){e.parts[m.j]=m.s;e.got++}
    if(e.got===e.n){this.snapIn.delete(m.id);unpackStr(m.z,e.parts.join('')).then(done).catch(err=>console.error('snapshot',err))}}
  beginGame(){newGame({seed:this.cfg.seed,diff:this.cfg.diff,humans:this.cfg.names.map(n=>({name:n}))});G.me=G.humans[this.seat];$('lobby').hidden=true;$('title').hidden=true;showBrief()}
  sayReady(){if(this.isHost){this.ready.add(0);this.checkGo()}else this.send({t:'ready'});$('briefGo').textContent='Waiting for the others…';$('briefGo').disabled=true}
  launch(){if(state==='brief'||state==='title'||state==='lobby'){$('brief').hidden=true;startPlay()}if(!this.lock){this.lock=new Lock(this,0);for(const b of this.early||[])this.lock.add(b.k,b.d);this.early=null}}
  sendInput(t,d){if(this.isHost)this.recvInput(0,t,d);else this.send({t:'i',k:t,d})}
  tickHash(t,h){if(this.isHost){this.hostH.set(t,h);this.checkHash(t)}else this.send({t:'h',k:t,h})}
  setAway(v){this.away=v;if(!this.isHost)this.send({t:'away',v})}
  away_(i){if(!this.started)return false;if(this.isHost)return i===0?this.away:!!(this.seats[i]&&(this.seats[i].away||!this.seats[i].connected));return this.wait.some(w=>w.startsWith((G.humans[i]||{}).name+' ('))}
  close(){this.closed=true;this.timers.forEach(t=>clearInterval(t));try{this.peer&&this.peer.destroy()}catch(e){}}}
function roomURL(code){const q=new URLSearchParams(location.search);q.set('room',code);return location.pathname+'?'+q}
function leaveRoom(keepURL){if(NET){if(NET.isHost&&!NET.started)store.del('ac_host_'+NET.code);NET.close();NET=null}if(keepURL)return;const q=new URLSearchParams(location.search);q.delete('room');history.replaceState(null,'',location.pathname+(q+''?'?'+q:''))}
document.addEventListener('visibilitychange',()=>{if(NET)NET.setAway(document.hidden)});

// ---------- lobby & away screens ----------
function lobbyUI(){if(!NET||NET.started)return;const L=$('lobby');if(L.hidden){$('title').hidden=true;L.hidden=false}
  const host=NET.isHost,seats=host?NET.seats.map(s=>({name:s.name,connected:s.connected,rtt:s.rtt})):(NET.lobby?NET.lobby.seats:[]);
  $('lbCode').textContent=NET.code;
  $('lbInfo').innerHTML=`${seats.length} of ${MAXH} players. ${MAXH-seats.length>0?`Bots fill the other ${MAXH-seats.length} seats. `:''}Roles are dealt at random — anyone could be the spy or the commissar.`;
  $('lbPlayers').innerHTML='<tr><th></th><th>Player</th><th>Ping</th></tr>'+seats.map((s,i)=>`<tr><td><span class="sw" style="background:${HCOL[i]}"></span></td><td>${esc(s.name)}${i===NET.seat?' (you)':''}${i===0?' · host':''}</td><td class="cal">${i===0?'—':s.rtt?s.rtt+' ms':'…'}</td></tr>`).join('')+
    Array.from({length:MAXH-seats.length},()=>`<tr><td></td><td style="color:var(--faint)">bot</td><td></td></tr>`).join('');
  document.querySelectorAll('#lbDiff button').forEach(x=>{x.setAttribute('aria-pressed',x.dataset.diff===NET.diff?'true':'false');x.disabled=!host});
  $('lbStart').hidden=!host;$('lbWait').hidden=host}
let awayKey='';
function awayUI(){const el=$('away');let txt='';
  if(NET&&NET.started&&G&&!G.over&&(state==='play'||state==='notebook'||state==='pause')){
    if(NET.resuming)txt='Rejoining the battle…';
    else if(!NET.isHost&&NET.hostLost)txt='Lost the connection to the host — reconnecting…';
    else if(NET.recovering)txt='Waiting for the other players to reconnect so the battle can resume…';
    else if(NET.lock&&NET.lock.stallT>0.5)txt='Paused — waiting for '+(NET.wait.length?listNames(NET.wait):'the other players')+'.'}
  if(txt!==awayKey){awayKey=txt;el.hidden=!txt;if(txt)$('awayTxt').textContent=txt}}

// ================= buttons =================
$('noteBtn').onclick=()=>openNotebook();$('nbClose').onclick=()=>closeNotebook();
$('roleSeg').addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;ROLE=b.dataset.role;document.querySelectorAll('#roleSeg button').forEach(x=>x.setAttribute('aria-pressed',x===b?'true':'false'))});
$('diffSeg').addEventListener('click',e=>{const b=e.target.closest('button');if(!b)return;DIFFSEL=b.dataset.diff;try{localStorage.setItem('ac_diff',DIFFSEL)}catch(e){}document.querySelectorAll('#diffSeg button').forEach(x=>x.setAttribute('aria-pressed',x===b?'true':'false'))});
document.querySelectorAll('#diffSeg button').forEach(x=>x.setAttribute('aria-pressed',x.dataset.diff===DIFFSEL?'true':'false'));
$('lbDiff').addEventListener('click',e=>{const b=e.target.closest('button');if(!b||!NET||!NET.isHost)return;NET.setDiff(b.dataset.diff)});
const myName=()=>{const n=$('nameIn').value.trim().slice(0,12)||'Rybakov';try{localStorage.setItem('ac_name',n)}catch(e){}return n};
try{const n=localStorage.getItem('ac_name');if(n)$('nameIn').value=n}catch(e){}
$('startBtn').onclick=()=>{audioInit();if(SND.ctx&&SND.ctx.state==='suspended')SND.ctx.resume();leaveRoom();newGame({seed:(crnd()*0x7fffffff)|0,diff:DIFFSEL,humans:[{name:myName()}],rolePref:ROLE});$('title').hidden=true;showBrief()};
function mpErr(e){$('mpMsg').textContent=e&&e.message?e.message:String(e);leaveRoom();toTitle()}
$('hostBtn').onclick=()=>{audioInit();if(!Room.ok()){$('mpMsg').textContent='Multiplayer needs WebRTC and could not load the connection library.';return}leaveRoom();$('mpMsg').textContent='Opening a room…';
  NET=new Room(myName());NET.hostNew(err=>{if(err)return mpErr(err);$('mpMsg').textContent='';history.replaceState(null,'',roomURL(NET.code));lobbyUI()})};
function joinCode(code){audioInit();if(!Room.ok()){$('mpMsg').textContent='Multiplayer needs WebRTC and could not load the connection library.';return}code=String(code||'').trim().toUpperCase();if(code.length<4){$('mpMsg').textContent='Enter the 5-letter room code.';return}
  leaveRoom(true);$('mpMsg').textContent='Connecting…';NET=new Room(myName());history.replaceState(null,'',roomURL(code));NET.join(code,err=>{if(err)return mpErr(err);$('mpMsg').textContent='';history.replaceState(null,'',roomURL(NET.code));lobbyUI()})}
$('joinBtn').onclick=()=>joinCode($('codeIn').value);
$('codeIn').addEventListener('keydown',e=>{if(e.key==='Enter')joinCode($('codeIn').value)});
$('lbStart').onclick=()=>{if(NET&&NET.isHost)NET.startGame()};
$('lbLeave').onclick=()=>{leaveRoom();toTitle()};
$('lbCopy').onclick=()=>{const url=location.origin+roomURL(NET.code);try{navigator.clipboard.writeText(url);$('lbCopy').textContent='Link copied'}catch(e){$('lbCopy').textContent=url}};
$('briefGo').onclick=()=>{if(NET)NET.sayReady();else startPlay()};
$('resumeBtn').onclick=()=>{$('pause').hidden=true;state='play'};
$('quitBtn').onclick=()=>{if(NET&&NET.started&&NET.isHost)store.del('ac_host_'+NET.code);leaveRoom();toTitle()};
$('awayLeave').onclick=()=>{leaveRoom();toTitle()};
$('muteBtn').onclick=()=>{SND.muted=!SND.muted;$('muteBtn').textContent=SND.muted?'Sound off':'Sound on';if(SND.master)SND.master.gain.value=SND.muted?0:0.45};
$('againBtn').onclick=()=>{if(NET&&NET.isHost)store.del('ac_host_'+NET.code);leaveRoom();toTitle()};

// ================= boot =================
let last=performance.now();
function frame(now){const dt=Math.min(0.25,(now-last)/1000);last=now;SND.budget=0;
  try{if(window.__acFreeze){requestAnimationFrame(frame);return}if(NET&&NET.lock)NET.lock.pump(dt);else Solo.pump(dt);
    if(G&&G.over&&G.result&&state!=='over'&&state!=='title')showEnd();
    RALPHA=clamp((now-lastStepAt)/(DT*1000),0,1);
    if(G){updateFx(Math.min(dt,0.05));withLerp(render);if(state!=='title'&&G.me){hudTick(dt);councilUI()}awayUI()}}catch(err){console.error(err)}
  requestAnimationFrame(frame)}
async function boot(){resize();if(TOUCH)document.body.classList.add('touch');
  try{await Promise.race([Promise.all([document.fonts.load('20px "Russo One"'),document.fonts.load('14px "PT Sans"'),document.fonts.load('14px "PT Mono"')]),new Promise(r=>setTimeout(r,2500))])}catch(e){}
  bake();toTitle();requestAnimationFrame(frame);
  // invite links (?room=CODE) join straight away; a host who reloads mid-battle takes the room back
  const code=(new URLSearchParams(location.search).get('room')||'').toUpperCase();
  if(code){$('codeIn').value=code;const rec=store.get('ac_host_'+code);
    if(rec&&Room.ok()&&Date.now()-(rec.at||0)<6*3600e3){$('mpMsg').textContent='Reopening your room…';NET=new Room(myName());NET.hostRecover(rec,err=>{if(err)return mpErr(err);$('mpMsg').textContent='';$('title').hidden=true;$('hud').hidden=false;state='play';
        newGame({seed:rec.cfg.seed,diff:rec.cfg.diff,humans:rec.cfg.names.map(n=>({name:n}))});G.me=G.humans[0]})}
    else if(Room.ok())joinCode(code)}
  window.__ac={G:()=>G,state:()=>state,net:()=>NET,hh:()=>[...HHIST],step,serialize,stateHash,desync(){if(G&&G.me){G.me.x+=0.01}}}}
boot();
})();
