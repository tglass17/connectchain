const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto');
const {WebSocketServer}=require('ws');const filter=require('leo-profanity');
const PORT=process.env.PORT||3000,OWNER='guynamedtucker',DB='data.json';
let db={users:{},tokens:{},ownerTag:{c1:'#ff0080',c2:'#00d4ff'}};try{db=JSON.parse(fs.readFileSync(DB))}catch{}db.tags=db.tags||{};
const RURL=process.env.UPSTASH_REDIS_REST_URL,RTOK=process.env.UPSTASH_REDIS_REST_TOKEN;
const rcmd=a=>fetch(RURL,{method:'POST',headers:{Authorization:'Bearer '+RTOK},body:JSON.stringify(a)}).then(r=>r.json());
const flush=()=>{const d=JSON.stringify(db);fs.writeFile(DB,d,()=>{});if(RURL)rcmd(['SET','connectchain',d]).catch(e=>console.log('remote save failed',e.message))};
let st=0;const save=()=>{if(!st)st=setTimeout(()=>{st=0;flush()},RURL?10000:500)};
process.on('unhandledRejection',e=>console.log('unhandled rejection:',e&&e.message));
process.on('SIGTERM',()=>{flush();setTimeout(()=>process.exit(0),1500)});
const hash=(p,s)=>crypto.scryptSync(p,s,32).toString('hex');
const mk=(n,p)=>{const salt=crypto.randomBytes(8).toString('hex');return{name:n,salt,hash:hash(p,salt),xp:0,bal:0,mult:1,color:'white',tag:'',owner:n===OWNER}};
function ensureOwner(){const pw=process.env.OWNER_PASSWORD;if(!pw)return;if(!db.users[OWNER]){db.users[OWNER]=mk(OWNER,pw);db.users[OWNER].tag='OWNER'}else db.users[OWNER].hash=hash(pw,db.users[OWNER].salt);save()}
const COLORS=[['white',0],['blue',200],['red',300],['yellow',400],['green',500],['blueg',600],['orange',700],['redorangeg',800],['greenhaze',1200],['rainbow',3000],['purplehaze',7000]];
const SHOP={'1.5':500,'2':1000};
const WORDS=['cat','school','pizza','fire','water','money','space','music','computer','forest','hospital','dragon','phone','ocean','mountain','movie','sports','history','chocolate','train'];
const online=new Map(),bans={};let clients=new Set();
const send=(c,o)=>c.ws.readyState===1&&c.ws.send(JSON.stringify(o));
const pub=u=>{const t=u.owner?null:db.tags[u.name.toLowerCase()];return{name:u.name,dn:u.display||u.name,xp:u.xp,color:u.color,tag:t?t.text:u.tag,tc1:t&&t.c1,tc2:t&&t.c2,owner:!!u.owner,mod:!!u.mod,alpha:!!u.alpha,rv:!!u.reqview,re:!!u.reqedit}};
const dn=u=>u.display||u.name;
const specState=bt=>({t:'spec',p:bt.p.map(c=>pub(c.u)),chain:bt.chain,lives:bt.lives,turn:bt.turn,live:bt.live});
const me=c=>({...pub(c.u),bal:c.u.bal,mult:c.u.mult,account:!!c.acct});
function lobby(){const l=[...online.values()].map(c=>({...pub(c.u),busy:!!c.bt,away:!!c.inact,endless:!!c.end,acct:!!c.acct}));for(const c of online.values())send(c,{t:'lobby',list:l,ownerTag:db.ownerTag})}
const addXp=(c,n)=>{if(!c.u.owner){c.u.xp+=n;c.u.bal+=n;gain(c.u,n)}if(c.acct)save();send(c,{t:'me',me:me(c)})};
const flash=(c,text,kind)=>send(c,{t:'flash',text,kind});
function login(c,u,acct){if(c.u)logout(c);c.u=u;c.acct=acct;c.lastAct=Date.now();c.inact=false;c.hiddenSince=0;online.set(u.name.toLowerCase(),c);send(c,{t:'me',me:me(c),colors:COLORS,shop:SHOP});lobby();if(poll&&!poll.done)sendPoll(c);onLogin(c)}
function logout(c){if(c.end)finishEnd(c,false);if(c.watch){c.watch.spec.delete(c);c.watch=null}if(c.pend){clearTimeout(c.pend.tm);c.pend=null}if(c.u)online.delete(c.u.name.toLowerCase());end(c,false);c.u=null;lobby()}
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
 const w=won?c:o;bt.spec.forEach(s=>{s.watch=null;send(s,{t:'specover',winner:w.u?dn(w.u):'?'})});bt.spec.clear();if(w.u){addXp(w,Math.round(100*w.u.mult));send(w,{t:'over',win:true});send(w===c?o:c,{t:'over',win:false})}lobby()}
function strike(c){c.strikes=(c.strikes||0)+1;if(c.strikes>=3){bans[c.ip]=Date.now()+6e5;send(c,{t:'banned'});c.ws.close()}
 else flash(c,c.strikes==2?'⚠ FINAL WARNING: keep it up and you will be banned.':'⚠ Warning: that word is not allowed.','warn')}
async function submit(c,w){const bt=c.bt;if(!bt||!bt.live||bt.p[bt.turn]!==c||bt.busy)return;
 w=String(w).toLowerCase().trim();if(!/^[a-z]{2,20}$/.test(w))return flash(c,'One word, letters only');
 if(filter.check(w)){flash(c,'That word does not count.','bad');return strike(c)}
 bt.busy=true;const ok=!bt.chain.includes(w)&&await rel(bt.chain.at(-1),w);bt.busy=false;if(!c.bt)return;
 const i=bt.p.indexOf(c);
 if(ok){bt.chain.push(w);bt.turn=1-i;addXp(c,Math.round(10*c.u.mult));push(bt);return}
 flash(c,'That is unrelated!','bad');bt.spec.forEach(s=>send(s,{t:'specmsg',text:dn(c.u)+' said "'+w+'" - unrelated!'}));bt.lives[i]--;
 if(bt.lives[i]<=0)return end(bt.p[1-i],true);reset(bt,1-i)}
const find=n=>online.get(String(n).toLowerCase());
function target(n){const c=find(n);if(c)return{c,u:c.u};const u=Object.values(db.users).find(x=>x.name.toLowerCase()==String(n).toLowerCase());return u&&{u}}
const okName=n=>/^[A-Za-z0-9_]{3,16}$/.test(n)&&!filter.check(n);
const TZ=process.env.TZ_NAME||'America/New_York',IDLE=+process.env.IDLE_MS||33*60000,HID=+process.env.HIDDEN_MS||60000,TICK=+process.env.TICK_MS||15000;
const ymd=()=>new Date().toLocaleDateString('en-CA',{timeZone:TZ});
function wk(d){const t=new Date(d+'T00:00:00Z');t.setUTCDate(t.getUTCDate()-(t.getUTCDay()+6)%7);return t.toISOString().slice(0,10)}
function roll(u){const d=ymd(),w=wk(d),m=d.slice(0,7),g=u.g=u.g||{d,dx:0,w,wx:0,m,mx:0};if(g.d!==d){g.d=d;g.dx=0}if(g.w!==w){g.w=w;g.wx=0}if(g.m!==m){g.m=m;g.mx=0}return g}
const gain=(u,n)=>{if(!n||u.owner||db.users[u.name]!==u)return;const g=roll(u);g.dx=Math.max(0,g.dx+n);g.wx=Math.max(0,g.wx+n);g.mx=Math.max(0,g.mx+n)};
function lbData(){const us=Object.values(db.users),top=f=>us.map(u=>({u,v:f(u)})).filter(x=>x.v>0).sort((a,b)=>b.v-a.v).slice(0,10).map(x=>({...pub(x.u),v:Math.round(x.v)}));
 return{day:top(u=>u.owner?0:roll(u).dx),week:top(u=>u.owner?0:roll(u).wx),month:top(u=>u.owner?0:roll(u).mx),all:top(u=>u.owner?0:u.xp),time:top(u=>u.secs||0)}}
let tk=0;setInterval(()=>{const now=Date.now();let ch=false;for(const c of online.values()){if(!c.lastAct)c.lastAct=now;
 if(!c.inact&&((c.hiddenSince&&now-c.hiddenSince>HID)||(now-c.lastAct>IDLE&&!c.bt&&!c.watch))){c.inact=true;ch=true}
 if(c.u&&c.acct&&!c.inact)c.u.secs=(c.u.secs||0)+TICK/1000}
 if(ch)lobby();if(++tk%8==0)save()},TICK);
const canView=c=>c.u&&c.acct&&(c.u.owner||c.u.reqview||c.u.reqedit);
const canEdit=c=>c.u&&c.acct&&(c.u.owner||c.u.reqedit);
const reqOf=n=>[...db.modreqs].reverse().find(r=>r.name.toLowerCase()==String(n).toLowerCase());
const reqList=()=>db.modreqs.slice(-100).map(r=>({id:r.id,name:r.name,dn:dn(db.users[r.name]||{name:r.name}),reason:r.reason,at:r.at,status:r.status,replies:r.replies}));
const pushReqs=()=>{const l=reqList();for(const x of online.values())if(canView(x))send(x,{t:'modreqs',list:l})};
const lc=s=>String(s).toLowerCase();
const isMem=(r,n)=>r.members.some(x=>lc(x)==lc(n));
const acctName=n=>Object.keys(db.users).find(k=>lc(k)==lc(n));
const mview=n=>({name:n,dn:dn(db.users[n]||{name:n})});
const roomsFor=n=>Object.values(db.rooms).filter(r=>isMem(r,n));
const rsum=(r,n)=>{const l=r.msgs[r.msgs.length-1];return{id:r.id,name:r.name,members:r.members.map(mview),last:l?{dn:l.dn,text:l.text.slice(0,50),at:l.at}:null,at:l?l.at:r.created,unread:r.msgs.filter(m=>m.at>(r.read[lc(n)]||0)&&lc(m.u)!=lc(n)).length}};
const rfull=r=>({id:r.id,name:r.name,members:r.members.map(mview),msgs:r.msgs.slice(-100)});
function pushRooms(names){for(const x of online.values())if(x.acct&&x.u&&names.some(n=>lc(n)==lc(x.u.name)))send(x,{t:'rooms',list:roomsFor(x.u.name).map(r=>rsum(r,x.u.name)).sort((a,b)=>b.at-a.at)})}
const toMembers=(r,msg)=>{for(const x of online.values())if(x.acct&&x.u&&isMem(r,x.u.name))send(x,msg)};
const ideaList=()=>db.ideas.slice(-100).map(r=>({id:r.id,name:r.name,dn:r.dn,text:r.text,at:r.at,acked:r.acked,handled:r.handled,replies:r.replies}));
const pushIdeas=()=>{for(const x of online.values())if(x.u&&x.acct&&x.u.owner)send(x,{t:'ideas',list:ideaList()})};
function inboxAdd(name,acct,item){const c=find(name);let u=null;if(c&&c.acct===acct)u=c.u;else if(acct)u=db.users[name];if(!u)return;
 const inb=u.inbox=u.inbox||[];inb.push({id:Date.now()*1000+Math.floor(Math.random()*1000),read:false,at:Date.now(),...item});if(inb.length>50)inb.splice(0,inb.length-50);
 if(acct)save();if(c&&c.acct===acct)send(c,{t:'inbox',unread:inb.filter(x=>!x.read).length,new:item.text})}
function note(r,text){inboxAdd(r.name,true,{kind:'modreq',text})}
function onLogin(c){const un=(c.u.inbox||[]).filter(x=>!x.read).length;if(un)send(c,{t:'inbox',unread:un,new:'📬 You have '+un+' new inbox message'+(un>1?'s':'')});if(canView(c))send(c,{t:'modreqs',list:reqList()});if(c.u.owner)send(c,{t:'ideas',list:ideaList()});if(c.acct){pushRooms([c.u.name]);pushFriends([c.u.name])}if(isMod(c))send(c,{t:'reports',list:reportList(c)})}
let poll=null,pollT,pollBc;
const pkey=c=>c.u.name.toLowerCase();
function pview(){const counts=poll.opts.map(()=>0);Object.values(poll.votes).forEach(i=>counts[i]++);return{id:poll.id,q:poll.q,opts:poll.opts,counts,total:Object.keys(poll.votes).length,ms:Math.max(0,poll.endsAt-Date.now()),done:poll.done,by:poll.by}}
function sendPoll(c){if(!poll||!c.u)return;send(c,{t:'poll',poll:pview(),mine:poll.votes[pkey(c)]})}
function bcPoll(){for(const x of online.values())sendPoll(x)}
function endPoll(){if(!poll||poll.done)return;poll.done=true;clearTimeout(pollT);bcPoll()}
const ENDCAP=500,ENDWORD=5,ENDBONUS=5,startWord=()=>WORDS[Math.random()*WORDS.length|0];
const esend=(c,msg)=>{const e=c.end;send(c,{t:'end',chain:e.chain,words:e.words,streak:e.streak,turn:e.turn,msg})};
const addEnd=(e,n)=>{e.xp=Math.min(ENDCAP,e.xp+n)};
function finishEnd(c,notify){const e=c.end;if(!e)return;c.end=null;const amt=Math.round(e.xp*c.u.mult);if(amt>0)addXp(c,amt);
 if(notify)send(c,{t:'endover',words:e.words,best:e.best,xp:amt,mult:c.u.mult,capped:e.xp>=ENDCAP});lobby()}
const STOP=new Set('the and has have had was were are been being not but for with from that this these those you your they them their its his her our out about into over than then just also very too more most some any all each every other such only own same what which who whom when where why how there here can will would should could may might must does did get got let say said'.split(' '));
const dmn=async(q,max)=>{const k='n|'+q+max;if(cache.has(k))return cache.get(k);try{const r=await fetch('https://api.datamuse.com/words?md=p&max='+max+'&'+q);const j=(await r.json()).filter(x=>x.tags&&x.tags.some(t=>t=='n')).map(x=>x.word);cache.set(k,j);return j}catch{return[]}};
async function botMove(c){const e=c.end;if(!e)return;const last=e.chain.at(-1);let pick=null;
 const okw=w=>/^[a-z]{3,12}$/.test(w)&&!STOP.has(w)&&!e.chain.includes(w)&&!w.startsWith(last)&&!last.startsWith(w)&&!filter.check(w);
 const pool=(await dmn('rel_trg='+last,25)).filter(okw).slice(0,14);
 for(let i=pool.length-1;i>0;i--){const j=Math.random()*(i+1)|0;[pool[i],pool[j]]=[pool[j],pool[i]]}
 const strong=[];for(const w of pool){if(strong.length>=4)break;if((await dmn('rel_trg='+w,150)).includes(last))strong.push(w)}
 for(const w of strong){if(c.end!==e)return;if(await rel(last,w)){pick=w;break}}
 if(!pick&&KEY)for(const w of pool.filter(x=>!strong.includes(x)).slice(0,3)){if(c.end!==e)return;if(await rel(last,w)){pick=w;break}}
 if(c.end!==e)return;
 if(!pick){addEnd(e,ENDBONUS);e.chain=[startWord()];e.streak=0;e.turn='you';return esend(c,'🤖 The bot is stumped and could not find a word! +'+ENDBONUS+' bonus XP. New word!')}
 e.chain.push(pick);e.turn='you';esend(c,'🤖 The bot said "'+pick+'"')}
const fuser=n=>db.users[acctName(n)||''];
const hasF=(u,n)=>(u.friends||[]).some(x=>lc(x)==lc(n));
const friendView=u=>{const v=n=>({name:n,dn:dn(db.users[n]||{name:n})});return{friends:(u.friends||[]).map(v),inc:(u.fin||[]).map(v),out:(u.fout||[]).slice()}};
function pushFriends(names){for(const x of online.values())if(x.acct&&x.u&&names.some(n=>lc(n)==lc(x.u.name)))send(x,{t:'friends',...friendView(x.u)})}
function makeFriends(a,b){for(const[u,o]of[[a,b],[b,a]]){u.friends=u.friends||[];if(!hasF(u,o.name))u.friends.push(o.name);u.fin=(u.fin||[]).filter(x=>lc(x)!=lc(o.name));u.fout=(u.fout||[]).filter(x=>lc(x)!=lc(o.name))}}
let evt=null,evtCool=0;const EV_START=4000,EV_DUR=15000,EV_COST=10000;
function startEvent(by){const coins=[];let t=0,id=0;while(t<EV_DUR){const big=Math.random()<0.08;coins.push({id:id++,t:Math.round(t),big,x:5+Math.random()*88,y:14+Math.random()*78,life:big?2800:3500});t+=170+Math.random()*90}
 let nb=coins.filter(c=>c.big).length;while(nb<4){const c=coins[Math.random()*coins.length|0];if(!c.big){c.big=true;c.life=2800;nb++}}
 const e=evt={id:Date.now(),coinsAt:Date.now()+EV_START,coins:new Map(coins.map(c=>[c.id,c])),claims:{}};evtCool=Date.now()+EV_START+EV_DUR+4500+60000;
 const msg={t:'tevent',id:e.id,startIn:EV_START,coins};for(const x of online.values())send(x,msg);
 setTimeout(()=>{if(evt===e)evt=null},EV_START+EV_DUR+4500)}
const RCATS=['player','name','chat','bug','other'];
const reportList=c=>db.reports.slice(-100).filter(r=>c.u.owner||!r.tmod).map(r=>({id:r.id,by:r.by,byDn:r.byDn,target:r.target,tdn:r.tdn,cat:r.cat,text:r.text,ctx:r.ctx,at:r.at,status:r.status}));
const pushReports=()=>{for(const x of online.values())if(isMod(x))send(x,{t:'reports',list:reportList(x)})};
const isMod=c=>c.u&&c.acct&&(c.u.owner||c.u.mod);
const canAnn=c=>c.u&&c.acct&&(c.u.owner||c.u.mod||c.u.alpha);
const canHit=(c,u)=>u!==c.u&&!u.owner&&(c.u.owner||!u.mod);
const banInfo=n=>{const k=String(n||'').toLowerCase(),b=db.bans[k];if(!b)return null;if(b.until&&b.until<Date.now()){delete db.bans[k];save();return null}return b};
const banMsg=b=>({t:'banned',manual:true,reason:b.reason||'',until:b.until||0});
const blocked=(c,n)=>{const b=banInfo(n);if(!b)return false;send(c,banMsg(b));setTimeout(()=>c.ws.close(),300);return true};
const handlers={
 guest(c,m){const n=String(m.name||'');if(blocked(c,n))return;if(!okName(n))return flash(c,'Name: 3-16 letters/numbers/_','bad');
  if(find(n)||Object.keys(db.users).some(k=>k.toLowerCase()==n.toLowerCase()))return flash(c,'Username taken','bad');
  login(c,{name:n,xp:0,bal:0,mult:1,color:'white',tag:''},false)},
 signup(c,m){const n=String(m.name||'');if(blocked(c,n))return;if(!okName(n)||String(m.pass||'').length<6)return flash(c,'Valid name + password (6+ chars) needed','bad');
  if(find(n)&&find(n)!==c||Object.keys(db.users).some(k=>k.toLowerCase()==n.toLowerCase()))return flash(c,'Username taken','bad');
  const u=mk(n,m.pass);u.owner=false;db.users[n]=u;const tk=crypto.randomBytes(24).toString('hex');db.tokens[tk]=n;save();login(c,u,true);send(c,{t:'token',tk})},
 login(c,m){if(blocked(c,m.name))return;const u=db.users[m.name];if(!u||hash(String(m.pass),u.salt)!==u.hash)return flash(c,'Wrong username or password','bad');
  const o=find(u.name);if(o&&o!==c){logout(o);o.ws.close()}
  const tk=crypto.randomBytes(24).toString('hex');db.tokens[tk]=u.name;save();login(c,u,true);send(c,{t:'token',tk})},
 resume(c,m){const n=db.tokens[m.tk],u=n&&db.users[n];if(!u)return send(c,{t:'badtoken'});if(blocked(c,n))return;const o=find(n);if(o&&o!==c){logout(o);o.ws.close()}login(c,u,true)},
 challenge(c,m){if(c.end)return flash(c,'Stop endless mode first','warn');const o=find(m.to);if(!o||o===c||o.bt||o.end||c.bt||c.pend)return;
  c.pend={to:o,tm:setTimeout(()=>{if(c.pend&&c.pend.to===o){c.pend=null;send(c,{t:'noresp',name:dn(o.u)});send(o,{t:'chalgone',from:c.u.name})}},20000)};
  send(o,{t:'challenge',from:c.u.name,dn:dn(c.u)})},
 deny(c,m){const o=find(m.from);if(!o||!o.pend||o.pend.to!==c)return;clearTimeout(o.pend.tm);o.pend=null;send(o,{t:'denied',name:dn(c.u)})},
 accept(c,m){if(c.end)return flash(c,'Stop endless mode first','warn');const o=find(m.from);if(!o||!o.pend||o.pend.to!==c||o.bt||c.bt)return;clearTimeout(o.pend.tm);o.pend=null;start(o,c)},
 typing(c,m){const bt=c.bt;if(!bt)return;const txt=filter.clean(String(m.text).slice(0,24)),i=bt.p.indexOf(c);send(bt.p[1-i],{t:'opptype',text:txt});bt.spec.forEach(s=>send(s,{t:'spectype',who:i,text:txt}))},
 watch(c,m){const o=find(m.who);if(!o||!o.bt||c.bt||c.end||c===o)return;if(c.watch)c.watch.spec.delete(c);c.watch=o.bt;o.bt.spec.add(c);send(c,specState(o.bt))},
 unwatch(c){if(c.watch){c.watch.spec.delete(c);c.watch=null}},
 setdisplay(c,m){const x=String(m.text||'').trim().replace(/\s+/g,' ');
  if(x){if(!/^[A-Za-z0-9_ .!-]{2,20}$/.test(x)||filter.check(x))return flash(c,'Display name: 2-20 letters, numbers, spaces, _ . ! - (no bad words)','bad');
   const lc=x.toLowerCase();if(lc!==c.u.name.toLowerCase()&&(Object.keys(db.users).some(k=>k.toLowerCase()==lc)||[...online.values()].some(o=>o!==c&&((o.u.display||'').toLowerCase()==lc||o.u.name.toLowerCase()==lc))))return flash(c,'That display name is taken','bad')}
  c.u.display=x;if(c.acct)save();send(c,{t:'me',me:me(c)});if(c.bt&&c.bt.live)push(c.bt);lobby()},
 submit(c,m){submit(c,m.word)},
 forfeit(c){end(c,false)},
 color(c,m){const k=COLORS.find(x=>x[0]==m.color),own=c.u.owner;if((k&&(own||c.u.xp>=k[1]))||(own&&m.color=='ownerrainbow')){c.u.color=m.color;if(c.acct)save();send(c,{t:'me',me:me(c)});lobby()}},
 buy(c,m){const p=SHOP[m.mult];if(p&&c.u.bal>=p&&c.u.mult<+m.mult){c.u.bal-=p;c.u.mult=+m.mult;if(c.acct)save();send(c,{t:'me',me:me(c)})}},
 announce(c,m){if(!canAnn(c))return;const t=String(m.text||'').trim().slice(0,140);if(!t||Date.now()-(c.lastAnn||0)<3000)return;c.lastAnn=Date.now();for(const x of online.values())send(x,{t:'announce',text:t,from:dn(c.u)})},
 warn(c,m){if(!isMod(c))return;const t=target(m.to);if(!t||!t.c||!canHit(c,t.u))return;const x=String(m.text||'').trim().slice(0,100)||'Please follow the rules.';t.u.warns=(t.u.warns||0)+1;if(t.c.acct)save();send(t.c,{t:'warned',text:x,count:t.u.warns,by:dn(c.u)})},
 ban(c,m){if(!isMod(c))return;const t=target(m.to);if(!t||!canHit(c,t.u))return;let mins=Math.floor(+m.mins)||0;mins=mins<=0?0:Math.min(mins,525600);const k=t.u.name.toLowerCase();db.bans[k]={until:mins?Date.now()+mins*6e4:0,reason:String(m.reason||'').slice(0,80),by:dn(c.u)};save();console.log('BAN',t.u.name,'by',c.u.name,'mins',mins);if(t.c){send(t.c,banMsg(db.bans[k]));setTimeout(()=>t.c.ws.close(),300)}send(c,{t:'flash',text:t.u.name+' banned',kind:'ok'})},
 unban(c,m){if(!isMod(c))return;delete db.bans[String(m.name||'').toLowerCase()];save();handlers.banlist(c)},
 banlist(c){if(!isMod(c))return;send(c,{t:'banlist',list:Object.entries(db.bans).filter(([k])=>banInfo(k)).map(([k,b])=>({name:k,until:b.until,reason:b.reason,by:b.by}))})},
 setmod(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t||t.u.owner||db.users[t.u.name]!==t.u)return;t.u.mod=!!m.on;save();if(t.c){send(t.c,{t:'me',me:me(t.c)});if(t.u.mod)send(t.c,{t:'reports',list:reportList(t.c)})}lobby()},
 friends(c){if(c.acct)send(c,{t:'friends',...friendView(c.u)})},
 friendreq(c,m){if(!c.acct)return flash(c,'Sign up for an account to add friends','bad');const tu=fuser(m.to);if(!tu)return flash(c,'You can only add players who have accounts','bad');if(tu===c.u||hasF(c.u,tu.name))return;
  if((c.u.fin||[]).some(x=>lc(x)==lc(tu.name))){makeFriends(c.u,tu);save();inboxAdd(tu.name,true,{kind:'friend',text:'🤝 '+dn(c.u)+' accepted your friend request!'});pushFriends([c.u.name,tu.name]);return flash(c,'You are now friends with '+dn(tu)+'!','ok')}
  if((c.u.fout||[]).some(x=>lc(x)==lc(tu.name)))return flash(c,'Friend request already sent','warn');
  (c.u.fout=c.u.fout||[]).push(tu.name);(tu.fin=tu.fin||[]).push(c.u.name);save();
  inboxAdd(tu.name,true,{kind:'friend',from:c.u.name,status:'pending',text:'👋 '+dn(c.u)+' sent you a friend request'});pushFriends([c.u.name,tu.name]);flash(c,'Friend request sent to '+dn(tu),'ok')},
 friendresp(c,m){if(!c.acct)return;const fu=fuser(m.from);if(!fu||!(c.u.fin||[]).some(x=>lc(x)==lc(fu.name)))return;
  for(const it of c.u.inbox||[])if(it.kind=='friend'&&it.from&&lc(it.from)==lc(fu.name)&&it.status=='pending')it.status=m.accept?'accepted':'declined';
  if(m.accept){makeFriends(c.u,fu);inboxAdd(fu.name,true,{kind:'friend',text:'🤝 '+dn(c.u)+' accepted your friend request!'})}
  else{c.u.fin=c.u.fin.filter(x=>lc(x)!=lc(fu.name));fu.fout=(fu.fout||[]).filter(x=>lc(x)!=lc(c.u.name))}
  save();pushFriends([c.u.name,fu.name]);if(m.fromInbox)handlers.inbox(c)},
 unfriend(c,m){if(!c.acct)return;const fu=fuser(m.name);if(!fu)return;c.u.friends=(c.u.friends||[]).filter(x=>lc(x)!=lc(fu.name));fu.friends=(fu.friends||[]).filter(x=>lc(x)!=lc(c.u.name));save();pushFriends([c.u.name,fu.name])},
 spawnevent(c){if(!c.u?.owner||!c.acct)return;if(evt)return flash(c,'A token explosion is already running','warn');startEvent(c.u)},
 buyevent(c){if(!c.u)return;if(c.u.owner)return flash(c,'You can spawn it free from the 🛠️ Tools button','ok');
  if(evt||Date.now()<evtCool)return flash(c,'A token explosion just ran or is running. Try again in a bit.','warn');
  if(c.u.bal<EV_COST||c.u.xp<EV_COST)return flash(c,'You need 10,000 XP to buy a Token Explosion','bad');
  c.u.xp-=EV_COST;c.u.bal-=EV_COST;gain(c.u,-EV_COST);{const k=COLORS.find(x=>x[0]==c.u.color);if(k&&c.u.xp<k[1])c.u.color='white'}if(c.acct)save();send(c,{t:'me',me:me(c)});startEvent(c.u)},
 coin(c,m){const e=evt;if(!e||m.ev!==e.id)return;const cn=e.coins.get(m.id|0);if(!cn)return;const now=Date.now()-e.coinsAt;if(now<cn.t-1500||now>cn.t+cn.life+2500)return;
  const k=lc(c.u.name)+(c.acct?'':'#g'),set=e.claims[k]=e.claims[k]||new Set();if(set.has(cn.id)||Date.now()-(c.lastCoin||0)<60)return;c.lastCoin=Date.now();set.add(cn.id);
  const xp=cn.big?100:10;addXp(c,xp);send(c,{t:'coinok',id:cn.id,xp,big:cn.big})},
 findacct(c,m){if(!c.u?.owner||!c.acct)return;const q=lc(String(m.q||'').trim()).slice(0,20);if(!q)return;
  send(c,{t:'acctfound',list:Object.values(db.users).filter(u=>!u.owner&&(lc(u.name).includes(q)||lc(u.display||'').includes(q))).slice(0,8).map(u=>({name:u.name,dn:dn(u),xp:u.xp||0,online:!!find(u.name)}))})},
 resetpw(c,m){if(!c.u?.owner||!c.acct)return;const u=fuser(m.to);if(!u||u.owner)return flash(c,'Only regular accounts can be reset','bad');
  const pw=crypto.randomBytes(6).toString('base64url');u.salt=crypto.randomBytes(8).toString('hex');u.hash=hash(pw,u.salt);
  for(const t of Object.keys(db.tokens))if(db.tokens[t]===u.name)delete db.tokens[t];
  const o=find(u.name);if(o&&o.acct){logout(o);o.ws.close()}save();console.log('PASSWORD RESET for',u.name,'by',c.u.name);send(c,{t:'pwreset',name:u.name,pw})},
 setpw(c,m){if(!c.acct||c.u.owner)return flash(c,'Only regular accounts can change their password here','bad');const np=String(m.np||'');
  if(hash(String(m.old||''),c.u.salt)!==c.u.hash)return flash(c,'Current password is wrong','bad');if(np.length<6||np.length>64)return flash(c,'New password must be 6-64 characters','bad');
  c.u.salt=crypto.randomBytes(8).toString('hex');c.u.hash=hash(np,c.u.salt);for(const t of Object.keys(db.tokens))if(db.tokens[t]===c.u.name)delete db.tokens[t];
  const tk=crypto.randomBytes(24).toString('hex');db.tokens[tk]=c.u.name;save();send(c,{t:'token',tk});flash(c,'Password changed!','ok')},
 report(c,m){const cat=RCATS.includes(m.cat)?m.cat:'other';let text=String(m.text||'').trim().slice(0,500);if(text.length<10)return flash(c,'Please describe the problem (10+ characters)','bad');
  if(Date.now()-(c.lastReport||0)<30000)return flash(c,'Please wait a bit before sending another report','warn');
  const raw=String(m.target||'').trim().slice(0,20);let target='',tu=null;
  if(/^[A-Za-z0-9_]{1,20}$/.test(raw)){const k=acctName(raw),o=find(raw);tu=k?db.users[k]:(o?o.u:null);target=tu?tu.name:raw}else if(raw)text=('(Mentioned: '+raw+') '+text).slice(0,520);
  if(tu&&tu===c.u)return flash(c,"You can't report yourself",'bad');
  if(db.reports.filter(r=>r.by===c.u.name&&r.status==='open').length>=10)return flash(c,'You already have 10 open reports. Thanks!','warn');
  const cx=m.ctx&&typeof m.ctx==='object'?{room:String(m.ctx.room||'').slice(0,40),msg:String(m.ctx.msg||'').slice(0,200)}:null;
  c.lastReport=Date.now();db.reports.push({id:Date.now()*1000+Math.floor(Math.random()*1000),by:c.u.name,byDn:dn(c.u),byAcct:!!c.acct,target,tdn:tu?dn(tu):target,tmod:!!(tu&&(tu.mod||tu.owner)),cat,text,ctx:cx,at:Date.now(),status:'open'});
  if(db.reports.length>300)db.reports=db.reports.slice(-300);save();pushReports();flash(c,'Report sent. Thank you!','ok')},
 reports(c){if(isMod(c))send(c,{t:'reports',list:reportList(c)})},
 reportdone(c,m){if(!isMod(c))return;const r=db.reports.find(x=>x.id===m.id);if(!r||r.status!=='open'||(r.tmod&&!c.u.owner))return;r.status='resolved';r.by2=dn(c.u);save();
  if(r.byAcct)inboxAdd(r.by,true,{kind:'report',text:'✅ Thanks! Your report'+(r.target?' about '+r.tdn:'')+' was reviewed by the team.'});pushReports()},
 signout(c,m){if(m.tk&&c.u&&db.tokens[m.tk]===c.u.name){delete db.tokens[m.tk];save()}logout(c);send(c,{t:'loggedout'})},
 endstart(c){if(c.bt||c.watch||c.end)return;if(c.pend){clearTimeout(c.pend.tm);c.pend=null}c.end={chain:[startWord()],xp:0,words:0,streak:0,best:0,turn:'you',busy:false};esend(c,'Go! Say a word that connects.');lobby()},
 async endsubmit(c,m){const e=c.end;if(!e||e.turn!=='you'||e.busy)return;const w=String(m.word||'').toLowerCase().trim();
  if(!/^[a-z]{2,20}$/.test(w))return flash(c,'One word, letters only','bad');
  if(filter.check(w)){flash(c,'That word does not count.','bad');return strike(c)}
  if(e.xp>=ENDCAP)return flash(c,'You hit the XP cap for this run. Press Stop to collect!','warn');
  e.busy=true;const ok=!e.chain.includes(w)&&await rel(e.chain.at(-1),w);e.busy=false;if(c.end!==e)return;
  if(!ok){flash(c,'That is unrelated!','bad');e.chain=[startWord()];e.streak=0;return esend(c,'Oops, that did not connect. New word!')}
  e.chain.push(w);e.words++;e.streak++;e.best=Math.max(e.best,e.streak);addEnd(e,ENDWORD);e.turn='bot';esend(c,'✅ Nice one!');setTimeout(()=>botMove(c),1000+Math.random()*1500)},
 endstop(c){finishEnd(c,true)},
 rooms(c){if(c.acct)pushRooms([c.u.name])},
 roomnew(c,m){if(!c.acct)return flash(c,'Sign up for an account to use chatrooms','bad');if(Date.now()-(c.lastRoom||0)<5000)return flash(c,'Slow down a little','warn');
  const name=String(m.name||'').trim().slice(0,30);if(!name||filter.check(name))return flash(c,'Give the chatroom a clean name (1-30 characters)','bad');
  if(roomsFor(c.u.name).length>=30)return flash(c,'You are in too many chatrooms','bad');
  const mem=[c.u.name],bad=[];for(const x of (Array.isArray(m.users)?m.users:[]).slice(0,19)){const q=String(x).trim();if(!q)continue;const k=acctName(q);if(!k)bad.push(q.slice(0,16));else if(!mem.some(y=>lc(y)==lc(k)))mem.push(k)}
  const id='r'+Date.now().toString(36)+Math.random().toString(36).slice(2,6);db.rooms[id]={id,name,members:mem,msgs:[],read:{[lc(c.u.name)]:Date.now()},created:Date.now(),by:c.u.name};c.lastRoom=Date.now();save();
  mem.slice(1).forEach(n=>inboxAdd(n,true,{kind:'room',text:'💬 '+dn(c.u)+' added you to the chatroom "'+name+'"'}));pushRooms(mem);send(c,{t:'room',room:rfull(db.rooms[id]),bad})},
 roomopen(c,m){const r=db.rooms[m.id];if(!c.acct||!r||!isMem(r,c.u.name))return;r.read[lc(c.u.name)]=Date.now();send(c,{t:'room',room:rfull(r)});pushRooms([c.u.name])},
 roomread(c,m){const r=db.rooms[m.id];if(c.acct&&r&&isMem(r,c.u.name)){r.read[lc(c.u.name)]=Date.now();save()}},
 roomsend(c,m){const r=db.rooms[m.id];if(!c.acct||!r||!isMem(r,c.u.name))return;const t=filter.clean(String(m.text||'').trim().slice(0,300));if(!t||Date.now()-(c.lastRmsg||0)<400)return;c.lastRmsg=Date.now();
  const msg={id:Date.now()*1000+Math.floor(Math.random()*1000),u:c.u.name,dn:dn(c.u),text:t,at:Date.now()};r.msgs.push(msg);if(r.msgs.length>200)r.msgs.splice(0,r.msgs.length-200);r.read[lc(c.u.name)]=Date.now();save();toMembers(r,{t:'rmsg',id:r.id,msg})},
 roomadd(c,m){const r=db.rooms[m.id];if(!c.acct||!r||!isMem(r,c.u.name))return;const added=[],bad=[];
  for(const x of (Array.isArray(m.users)?m.users:[]).slice(0,10)){const q=String(x).trim();if(!q)continue;const k=acctName(q);if(!k)bad.push(q.slice(0,16));else if(!isMem(r,k)&&r.members.length<20){r.members.push(k);added.push(k)}}
  if(added.length){save();added.forEach(n=>inboxAdd(n,true,{kind:'room',text:'💬 '+dn(c.u)+' added you to the chatroom "'+r.name+'"'}));pushRooms(r.members);toMembers(r,{t:'roommem',id:r.id,members:r.members.map(mview)})}
  send(c,{t:'roomadded',added,bad})},
 roomleave(c,m){const r=db.rooms[m.id];if(!c.acct||!r||!isMem(r,c.u.name))return;r.members=r.members.filter(x=>lc(x)!=lc(c.u.name));
  if(!r.members.length)delete db.rooms[r.id];else toMembers(r,{t:'roommem',id:r.id,members:r.members.map(mview)});save();pushRooms([c.u.name,...r.members])},
 idea(c,m){const text=String(m.text||'').trim().slice(0,300);if(text.length<10)return flash(c,'Please write at least 10 characters','bad');if(filter.check(text))return flash(c,'Please keep it clean','bad');
  if(Date.now()-(c.lastIdea||0)<30000)return flash(c,'Slow down! Wait a bit before sending another idea','warn');
  if(db.ideas.filter(i=>i.name===c.u.name&&i.acct===!!c.acct&&!i.handled).length>=5)return flash(c,'You already have 5 ideas waiting. Thanks!','warn');
  c.lastIdea=Date.now();db.ideas.push({id:Date.now()*1000+Math.floor(Math.random()*1000),name:c.u.name,dn:dn(c.u),acct:!!c.acct,text,at:Date.now(),acked:false,handled:false,replies:[]});if(db.ideas.length>300)db.ideas=db.ideas.slice(-300);save();pushIdeas();flash(c,'Idea sent! Thanks 💡','ok')},
 ideas(c){if(c.u.owner&&c.acct)send(c,{t:'ideas',list:ideaList()})},
 ideaact(c,m){if(!c.u?.owner||!c.acct)return;const r=db.ideas.find(x=>x.id===m.id);if(!r)return;const snip=r.text.length>60?r.text.slice(0,57)+'...':r.text,txt=String(m.text||'').trim().slice(0,300);
  if(m.act==='ack'){if(r.acked)return;r.acked=true;r.handled=true;inboxAdd(r.name,r.acct,{kind:'idea',text:'💡 '+dn(c.u)+' thought your idea was a good idea! "'+snip+'"'})}
  else if(m.act==='reply'&&txt){r.replies.push({by:dn(c.u),text:txt,at:Date.now()});r.handled=true;inboxAdd(r.name,r.acct,{kind:'idea',text:'💬 '+dn(c.u)+' replied to your idea "'+snip+'": '+txt})}
  else return;save();pushIdeas()},
 inbox(c){const inb=c.u.inbox||[];send(c,{t:'inbox',unread:0,list:inb.slice().reverse()});if(inb.some(x=>!x.read)){inb.forEach(x=>x.read=true);if(c.acct)save()}},
 mymodreq(c){if(!c.acct)return flash(c,'Sign up for an account first to request mod','bad');const r=reqOf(c.u.name);let can=true,why='';
  if(c.u.mod||c.u.owner){can=false;why='You already have mod powers.'}
  else if(r&&r.status=='pending'){can=false;why='Your request is waiting for a decision.'}
  else if(r&&r.status=='denied'&&Date.now()-r.decidedAt<36e5){can=false;why='Your last request was denied. You can ask again in about '+Math.ceil((36e5-(Date.now()-r.decidedAt))/6e4)+' minutes.'}
  send(c,{t:'mymodreq',req:r?{reason:r.reason,status:r.status,replies:r.replies}:null,can,why})},
 modreq(c,m){if(!c.acct)return flash(c,'Sign up for an account first to request mod','bad');const reason=String(m.reason||'').trim().slice(0,300);
  if(reason.length<10)return flash(c,'Please write at least 10 characters explaining why','bad');if(filter.check(reason))return flash(c,'Please keep it clean','bad');
  const r=reqOf(c.u.name);if(c.u.owner||c.u.mod||(r&&r.status=='pending')||(r&&r.status=='denied'&&Date.now()-r.decidedAt<36e5))return;
  db.modreqs.push({id:Date.now()*1000+Math.floor(Math.random()*1000),name:c.u.name,reason,at:Date.now(),status:'pending',replies:[]});if(db.modreqs.length>300)db.modreqs=db.modreqs.slice(-300);save();pushReqs();flash(c,'Request sent! The owner will see it.','ok')},
 modreqs(c){if(canView(c))send(c,{t:'modreqs',list:reqList()})},
 modact(c,m){if(!canEdit(c))return;const r=db.modreqs.find(x=>x.id===m.id);if(!r||r.status!=='pending')return;const act=m.act,txt=String(m.text||'').trim().slice(0,300);
  if(act==='accept'){const u=db.users[r.name];if(!u||u.owner)return;u.mod=true;r.status='accepted';r.decidedAt=Date.now();const t=find(r.name);if(t)send(t,{t:'me',me:me(t)});note(r,'✅ Your mod request was accepted. You now have Mod powers!','accepted')}
  else if(act==='deny'){r.status='denied';r.decidedAt=Date.now();note(r,'❌ Your mod request was denied.','denied')}
  else if(act==='reply'&&txt){r.replies.push({by:dn(c.u),text:txt,at:Date.now()});note(r,'📩 '+dn(c.u)+' replied to your mod request: '+txt)}
  else return;save();pushReqs();lobby()},
 setreqedit(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t||t.u.owner||db.users[t.u.name]!==t.u)return;t.u.reqedit=!!m.on;save();if(t.c){send(t.c,{t:'me',me:me(t.c)});if(canView(t.c))send(t.c,{t:'modreqs',list:reqList()})}lobby()},
 setreqview(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t||t.u.owner||db.users[t.u.name]!==t.u)return;t.u.reqview=!!m.on;save();if(t.c){send(t.c,{t:'me',me:me(t.c)});if(canView(t.c))send(t.c,{t:'modreqs',list:reqList()})}lobby()},
 setalpha(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t||t.u.owner||db.users[t.u.name]!==t.u)return;t.u.alpha=!!m.on;save();if(t.c)send(t.c,{t:'me',me:me(t.c)});lobby()},
 scare(c,m){if(!isMod(c))return;const t=target(m.to);if(!t||!t.c||t.c===c)return;
  if(t.u.owner){if(!c.u.owner)send(c,{t:'selfdestruct'});return}
  const i=m.img;if(typeof i!=='string'||i.length>400000||!/^data:image\/(jpeg|png|webp);base64,[A-Za-z0-9+\/=]+$/.test(i))return;
  if(!c.u.owner&&Date.now()-(c.lastScare||0)<10000)return flash(c,'Wait a few seconds before another jumpscare','warn');c.lastScare=Date.now();send(t.c,{t:'scare',img:i})},
 addlife(c,m){if(!c.u?.owner||!c.acct)return;const bt=c.bt||c.watch;if(!bt||!bt.live)return;const i=m.i===1?1:0;bt.lives[i]=Math.min(10,bt.lives[i]+1);push(bt)},
 startpoll(c,m){if(!canAnn(c))return;const q=String(m.q||'').trim().slice(0,120),o=(Array.isArray(m.opts)?m.opts:[]).map(x=>String(x||'').trim().slice(0,40)).filter(Boolean).slice(0,4);
  if(!q||o.length<2)return flash(c,'A poll needs a question and at least 2 options','bad');
  const secs=Math.min(600,Math.max(15,Math.floor(+m.secs)||60));clearTimeout(pollT);poll={id:Date.now(),q,opts:o,votes:{},endsAt:Date.now()+secs*1000,done:false,by:dn(c.u)};pollT=setTimeout(endPoll,secs*1000);bcPoll()},
 endpoll(c){if(canAnn(c))endPoll()},
 vote(c,m){if(!poll||poll.done||Date.now()>poll.endsAt||m.id!==poll.id)return;const i=m.i|0;if(i<0||i>=poll.opts.length)return;poll.votes[pkey(c)]=i;clearTimeout(pollBc);pollBc=setTimeout(bcPoll,250)},
 active(c){c.lastAct=Date.now();if(c.inact){c.inact=false;lobby()}},
 vis(c,m){c.hiddenSince=m.hidden?Date.now():0},
 lb(c){if(Date.now()-(c.lbAt||0)<3000)return;c.lbAt=Date.now();send(c,{t:'lb',...lbData()})},
 grant(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t)return;const n=Math.max(-1e6,Math.min(1e6,+m.xp|0));t.u.xp=Math.max(0,t.u.xp+n);gain(t.u,n);{const k=COLORS.find(x=>x[0]==t.u.color);if(k&&!t.u.owner&&t.u.xp<k[1])t.u.color='white'}t.u.bal=Math.max(0,t.u.bal+n);save();if(t.c)send(t.c,{t:'me',me:me(t.c)});lobby()},
 settag(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t||t.u.owner)return;const h=/^#[0-9a-f]{6}$/i,k=t.u.name.toLowerCase(),x=String(m.text||'').slice(0,16);
  if(!x)delete db.tags[k];else db.tags[k]={text:x,c1:h.test(m.c1)?m.c1:'#dddddd',c2:h.test(m.c2)?m.c2:'#aaaaaa'};t.u.tag='';save();lobby()},
 ownertag(c,m){if(!c.u?.owner||!c.acct)return;const h=/^#[0-9a-f]{6}$/i;if(h.test(m.c1)&&h.test(m.c2)){db.ownerTag={c1:m.c1,c2:m.c2};save();lobby()}}};
const types={'.html':'text/html','.js':'text/javascript','.css':'text/css','.png':'image/png','.gif':'image/gif','.jpg':'image/jpeg','.webp':'image/webp','.svg':'image/svg+xml','.ico':'image/x-icon'};
const ASSETS=['projectile.png','projectexplosion.gif'];
const srv=http.createServer((q,r)=>{let u='/';try{u=decodeURIComponent(q.url.split('?')[0])}catch{}
 const rel=u=='/'?'index.html':path.normalize(u).replace(/^(\.\.[\/\\])+/,'');
 const nf=()=>{r.writeHead(404);r.end('Not found')};
 const tryRead=(f,next)=>fs.readFile(f,(e,d)=>{if(e)return next();r.writeHead(200,{'Content-Type':types[path.extname(f)]||'text/plain'});r.end(d)});
 tryRead(path.join(__dirname,'public',rel),()=>{const b=path.basename(rel);if(ASSETS.includes(b))tryRead(path.join(__dirname,b),nf);else nf()})});
new WebSocketServer({server:srv}).on('connection',(ws,req)=>{const ip=req.headers['x-forwarded-for']?.split(',')[0]||req.socket.remoteAddress;
 const c={ws,ip,u:null};if(bans[ip]>Date.now()){send(c,{t:'banned'});return ws.close()}
 ws.on('message',d=>{let m;try{m=JSON.parse(d)}catch{return}if(m.t!=='guest'&&m.t!=='signup'&&m.t!=='login'&&m.t!=='resume'&&!c.u)return;handlers[m.t]?.(c,m)});
 ws.on('close',()=>{if(c.u)logout(c)})});
(async()=>{if(RURL){try{const r=await rcmd(['GET','connectchain']);if(r.result)db=JSON.parse(r.result);console.log('Loaded saved data from Upstash')}catch(e){console.log('Upstash load failed, exiting so saved data is not overwritten:',e.message);process.exit(1)}}
 db.users=db.users||{};db.tokens=db.tokens||{};db.tags=db.tags||{};db.bans=db.bans||{};db.modreqs=db.modreqs||[];db.ideas=db.ideas||[];db.rooms=db.rooms||{};db.reports=db.reports||[];db.ownerTag=db.ownerTag||{c1:'#ff0080',c2:'#00d4ff'};
 ensureOwner();srv.listen(PORT,()=>console.log('ConnectChain on '+PORT))})();
