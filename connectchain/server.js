const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto');
const {WebSocketServer}=require('ws');const filter=require('leo-profanity');
const PORT=process.env.PORT||3000,OWNER='guynamedtucker',DB='data.json';
let db={users:{},tokens:{},ownerTag:{c1:'#ff0080',c2:'#00d4ff'}};try{db=JSON.parse(fs.readFileSync(DB))}catch{}db.tags=db.tags||{};
const RURL=process.env.UPSTASH_REDIS_REST_URL,RTOK=process.env.UPSTASH_REDIS_REST_TOKEN;
const rcmd=a=>fetch(RURL,{method:'POST',headers:{Authorization:'Bearer '+RTOK},body:JSON.stringify(a)}).then(r=>r.json());
const flush=()=>{const d=JSON.stringify(db);fs.writeFile(DB,d,()=>{});if(RURL)rcmd(['SET','connectchain',d]).catch(e=>console.log('remote save failed',e.message))};
let st=0;const save=()=>{if(!st)st=setTimeout(()=>{st=0;flush()},RURL?10000:500)};
process.on('SIGTERM',()=>{flush();setTimeout(()=>process.exit(0),1500)});
const hash=(p,s)=>crypto.scryptSync(p,s,32).toString('hex');
const mk=(n,p)=>{const salt=crypto.randomBytes(8).toString('hex');return{name:n,salt,hash:hash(p,salt),xp:0,bal:0,mult:1,color:'white',tag:'',owner:n===OWNER}};
function ensureOwner(){const pw=process.env.OWNER_PASSWORD;if(!pw)return;if(!db.users[OWNER]){db.users[OWNER]=mk(OWNER,pw);db.users[OWNER].tag='OWNER'}else db.users[OWNER].hash=hash(pw,db.users[OWNER].salt);save()}
const COLORS=[['white',0],['blue',200],['red',300],['yellow',400],['green',500],['blueg',600],['orange',700],['redorangeg',800],['greenhaze',1200],['rainbow',3000]];
const SHOP={'1.5':500,'2':1000};
const WORDS=['cat','school','pizza','fire','water','money','space','music','computer','forest','hospital','dragon','phone','ocean','mountain','movie','sports','history','chocolate','train'];
const online=new Map(),bans={};let clients=new Set();
const send=(c,o)=>c.ws.readyState===1&&c.ws.send(JSON.stringify(o));
const pub=u=>{const t=u.owner?null:db.tags[u.name.toLowerCase()];return{name:u.name,xp:u.xp,color:u.color,tag:t?t.text:u.tag,tc1:t&&t.c1,tc2:t&&t.c2,owner:!!u.owner}};
const specState=bt=>({t:'spec',p:bt.p.map(c=>pub(c.u)),chain:bt.chain,lives:bt.lives,turn:bt.turn,live:bt.live});
const me=c=>({...pub(c.u),bal:c.u.bal,mult:c.u.mult,account:!!c.acct});
function lobby(){const l=[...online.values()].map(c=>({...pub(c.u),busy:!!c.bt}));for(const c of online.values())send(c,{t:'lobby',list:l,ownerTag:db.ownerTag})}
const addXp=(c,n)=>{if(!c.u.owner){c.u.xp+=n;c.u.bal+=n}if(c.acct)save();send(c,{t:'me',me:me(c)})};
const flash=(c,text,kind)=>send(c,{t:'flash',text,kind});
function login(c,u,acct){if(c.u)logout(c);c.u=u;c.acct=acct;online.set(u.name.toLowerCase(),c);send(c,{t:'me',me:me(c),colors:COLORS,shop:SHOP});lobby()}
function logout(c){if(c.watch){c.watch.spec.delete(c);c.watch=null}if(c.pend){clearTimeout(c.pend.tm);c.pend=null}if(c.u)online.delete(c.u.name.toLowerCase());end(c,false);c.u=null}
const cache=new Map();
async function dm(q,max){const k=q+max;if(cache.has(k))return cache.get(k);try{const r=await fetch('https://api.datamuse.com/words?max='+max+'&'+q);const j=(await r.json()).map(x=>x.word);cache.set(k,j);return j}catch{return[]}}
const KINDS=[['rel_trg',300],['rel_bga',150],['rel_bgb',150],['ml',60],['rel_syn',60],['rel_gen',60],['rel_spc',60],['rel_com',60],['rel_par',60]];
const relset=async w=>new Set((await Promise.all(KINDS.map(([k,m])=>dm(k+'='+w,m)))).flat());
async function relOld(a,b){const[A,B]=await Promise.all([relset(a),relset(b)]);return A.has(b)||B.has(a)}
const KEY=process.env.ANTHROPIC_API_KEY,aiCache=new Map();
const SYS='You judge a word-association game. Answer only YES or NO. YES if the second word is reasonably connected to the first: same topic, part of it, used with it, commonly paired, cause or effect, synonym, opposite, or a well-known phrase. NO if the link is a stretch or they are unrelated. Be fair but not too lenient.';
async function ai(a,b){const r=await fetch('https://api.anthropic.com/v1/messages',{method:'POST',headers:{'content-type':'application/json','x-api-key':KEY,'anthropic-version':'2023-06-01'},body:JSON.stringify({model:'claude-haiku-5-5',max_tokens:5,system:SYS,messages:[{role:'user',content:'First word: '+a+'\nSecond word: '+b}]})});
 const j=await r.json(),t=j.content&&j.content[0]&&j.content[0].text;if(!t)throw new Error('no answer');return /^\s*yes/i.test(t)}
async function rel(a,b){if(KEY){const k=a+'|'+b;if(aiCache.has(k))return aiCache.get(k);try{const v=await ai(a,b);aiCache.set(k,v);return v}catch(e){console.log('AI check failed, using word list',e.message)}}return relOld(a,b)}
function start(a,b){const bt={p:[a,b],lives:[3,3],chain:[],turn:0,live:false,spec:new Set()};[a,b].forEach(x=>{if(x.watch){x.watch.spec.delete(x);x.watch=null}});a.bt=b.bt=bt;
 bt.p.forEach((c,i)=>send(c,{t:'countdown',opp:pub(bt.p[1-i].u)}));lobby();
 setTimeout(()=>{if(a.bt===bt){bt.live=true;reset(bt,Math.round(Math.random()))}},4200)}
function reset(bt,turn){bt.chain=[WORDS[Math.random()*WORDS.length|0]];bt.turn=turn;push(bt)}
function push(bt){bt.p.forEach((c,i)=>send(c,{t:'battle',opp:pub(bt.p[1-i].u),chain:bt.chain,lives:bt.lives,you:i,turn:bt.turn}));bt.spec.forEach(s=>send(s,specState(bt)))}
function end(c,won){const bt=c.bt;if(!bt)return;const i=bt.p.indexOf(c),o=bt.p[1-i];bt.p.forEach(x=>{x.bt=null});
 const w=won?c:o;bt.spec.forEach(s=>{s.watch=null;send(s,{t:'specover',winner:w.u?w.u.name:'?'})});bt.spec.clear();if(w.u){addXp(w,Math.round(100*w.u.mult));send(w,{t:'over',win:true});send(w===c?o:c,{t:'over',win:false})}lobby()}
function strike(c){c.strikes=(c.strikes||0)+1;if(c.strikes>=3){bans[c.ip]=Date.now()+6e5;send(c,{t:'banned'});c.ws.close()}
 else flash(c,c.strikes==2?'⚠ FINAL WARNING: keep it up and you will be banned.':'⚠ Warning: that word is not allowed.','warn')}
async function submit(c,w){const bt=c.bt;if(!bt||!bt.live||bt.p[bt.turn]!==c||bt.busy)return;
 w=String(w).toLowerCase().trim();if(!/^[a-z]{2,20}$/.test(w))return flash(c,'One word, letters only');
 if(filter.check(w)){flash(c,'That word does not count.','bad');return strike(c)}
 bt.busy=true;const ok=!bt.chain.includes(w)&&await rel(bt.chain.at(-1),w);bt.busy=false;if(!c.bt)return;
 const i=bt.p.indexOf(c);
 if(ok){bt.chain.push(w);bt.turn=1-i;addXp(c,Math.round(10*c.u.mult));push(bt);return}
 flash(c,'That is unrelated!','bad');bt.spec.forEach(s=>send(s,{t:'specmsg',text:c.u.name+' said "'+w+'" - unrelated!'}));bt.lives[i]--;
 if(bt.lives[i]<=0)return end(bt.p[1-i],true);reset(bt,1-i)}
const find=n=>online.get(String(n).toLowerCase());
function target(n){const c=find(n);if(c)return{c,u:c.u};const u=Object.values(db.users).find(x=>x.name.toLowerCase()==String(n).toLowerCase());return u&&{u}}
const okName=n=>/^[A-Za-z0-9_]{3,16}$/.test(n)&&!filter.check(n);
const handlers={
 guest(c,m){const n=String(m.name||'');if(!okName(n))return flash(c,'Name: 3-16 letters/numbers/_','bad');
  if(find(n)||Object.keys(db.users).some(k=>k.toLowerCase()==n.toLowerCase()))return flash(c,'Username taken','bad');
  login(c,{name:n,xp:0,bal:0,mult:1,color:'white',tag:''},false)},
 signup(c,m){const n=String(m.name||'');if(!okName(n)||String(m.pass||'').length<6)return flash(c,'Valid name + password (6+ chars) needed','bad');
  if(find(n)&&find(n)!==c||Object.keys(db.users).some(k=>k.toLowerCase()==n.toLowerCase()))return flash(c,'Username taken','bad');
  const u=mk(n,m.pass);u.owner=false;db.users[n]=u;const tk=crypto.randomBytes(24).toString('hex');db.tokens[tk]=n;save();login(c,u,true);send(c,{t:'token',tk})},
 login(c,m){const u=db.users[m.name];if(!u||hash(String(m.pass),u.salt)!==u.hash)return flash(c,'Wrong username or password','bad');
  if(find(u.name)&&find(u.name)!==c)return flash(c,'Already logged in elsewhere','bad');
  const tk=crypto.randomBytes(24).toString('hex');db.tokens[tk]=u.name;save();login(c,u,true);send(c,{t:'token',tk})},
 resume(c,m){const n=db.tokens[m.tk],u=n&&db.users[n];if(!u||find(n))return;login(c,u,true)},
 challenge(c,m){const o=find(m.to);if(!o||o===c||o.bt||c.bt||c.pend)return;
  c.pend={to:o,tm:setTimeout(()=>{if(c.pend&&c.pend.to===o){c.pend=null;send(c,{t:'noresp',name:o.u.name});send(o,{t:'chalgone',from:c.u.name})}},20000)};
  send(o,{t:'challenge',from:c.u.name})},
 deny(c,m){const o=find(m.from);if(!o||!o.pend||o.pend.to!==c)return;clearTimeout(o.pend.tm);o.pend=null;send(o,{t:'denied',name:c.u.name})},
 accept(c,m){const o=find(m.from);if(!o||!o.pend||o.pend.to!==c||o.bt||c.bt)return;clearTimeout(o.pend.tm);o.pend=null;start(o,c)},
 typing(c,m){const bt=c.bt;if(!bt)return;const txt=filter.clean(String(m.text).slice(0,24)),i=bt.p.indexOf(c);send(bt.p[1-i],{t:'opptype',text:txt});bt.spec.forEach(s=>send(s,{t:'spectype',who:i,text:txt}))},
 watch(c,m){const o=find(m.who);if(!o||!o.bt||c.bt||c===o)return;if(c.watch)c.watch.spec.delete(c);c.watch=o.bt;o.bt.spec.add(c);send(c,specState(o.bt))},
 unwatch(c){if(c.watch){c.watch.spec.delete(c);c.watch=null}},
 submit(c,m){submit(c,m.word)},
 forfeit(c){end(c,false)},
 color(c,m){const k=COLORS.find(x=>x[0]==m.color);if(k&&c.u.xp>=k[1]){c.u.color=k[0];if(c.acct)save();send(c,{t:'me',me:me(c)});lobby()}},
 buy(c,m){const p=SHOP[m.mult];if(p&&c.u.bal>=p&&c.u.mult<+m.mult){c.u.bal-=p;c.u.mult=+m.mult;if(c.acct)save();send(c,{t:'me',me:me(c)})}},
 grant(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t)return;const n=Math.max(-1e6,Math.min(1e6,+m.xp|0));t.u.xp=Math.max(0,t.u.xp+n);t.u.bal=Math.max(0,t.u.bal+n);save();if(t.c)send(t.c,{t:'me',me:me(t.c)});lobby()},
 settag(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t||t.u.owner)return;const h=/^#[0-9a-f]{6}$/i,k=t.u.name.toLowerCase(),x=String(m.text||'').slice(0,16);
  if(!x)delete db.tags[k];else db.tags[k]={text:x,c1:h.test(m.c1)?m.c1:'#dddddd',c2:h.test(m.c2)?m.c2:'#aaaaaa'};t.u.tag='';save();lobby()},
 ownertag(c,m){if(!c.u?.owner||!c.acct)return;const h=/^#[0-9a-f]{6}$/i;if(h.test(m.c1)&&h.test(m.c2)){db.ownerTag={c1:m.c1,c2:m.c2};save();lobby()}}};
const types={'.html':'text/html','.js':'text/javascript','.css':'text/css'};
const srv=http.createServer((q,r)=>{let f=path.join(__dirname,'public',q.url=='/'?'index.html':path.normalize(q.url).replace(/^(\.\.[\/\\])+/,''));
 fs.readFile(f,(e,d)=>{if(e){r.writeHead(404);return r.end('Not found')}r.writeHead(200,{'Content-Type':types[path.extname(f)]||'text/plain'});r.end(d)})});
new WebSocketServer({server:srv}).on('connection',(ws,req)=>{const ip=req.headers['x-forwarded-for']?.split(',')[0]||req.socket.remoteAddress;
 const c={ws,ip,u:null};if(bans[ip]>Date.now()){send(c,{t:'banned'});return ws.close()}
 ws.on('message',d=>{let m;try{m=JSON.parse(d)}catch{return}if(m.t!=='guest'&&m.t!=='signup'&&m.t!=='login'&&m.t!=='resume'&&!c.u)return;handlers[m.t]?.(c,m)});
 ws.on('close',()=>{if(c.u)logout(c)})});
(async()=>{if(RURL){try{const r=await rcmd(['GET','connectchain']);if(r.result)db=JSON.parse(r.result);console.log('Loaded saved data from Upstash')}catch(e){console.log('Upstash load failed, exiting so saved data is not overwritten:',e.message);process.exit(1)}}
 db.users=db.users||{};db.tokens=db.tokens||{};db.tags=db.tags||{};db.ownerTag=db.ownerTag||{c1:'#ff0080',c2:'#00d4ff'};
 ensureOwner();srv.listen(PORT,()=>console.log('ConnectChain on '+PORT))})();
