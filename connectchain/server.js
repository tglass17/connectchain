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
const canPay=(u,p)=>u.bal>=p&&u.xp>=p;
function spend(u,p){u.xp-=p;u.bal-=p;gain(u,-p);{const k=COLORS.find(x=>x[0]==u.color);if(k&&!u.owner&&u.xp<k[1])u.color='white'}}
const THX_ID='l_harvestfeast',THX_PRICE=8000,RB_PRICE=4000,THX_DAYS=7;
const WORDS=['cat','school','pizza','fire','water','money','space','music','computer','forest','hospital','dragon','phone','ocean','mountain','movie','sports','history','chocolate','train','tree'];
const online=new Map(),bans={};let clients=new Set();
const send=(c,o)=>c.ws.readyState===1&&c.ws.send(JSON.stringify(o));
const pub=u=>{const t=u.owner?null:db.tags[u.name.toLowerCase()];return{name:u.name,dn:u.display||u.name,xp:u.xp,color:u.color,tag:t?t.text:u.tag,clan:u.clan&&db.clans&&db.clans[u.clan]?db.clans[u.clan].name:'',tc1:t&&t.c1,tc2:t&&t.c2,owner:!!u.owner,mod:!!u.mod,alpha:!!u.alpha,rv:!!u.reqview,re:!!u.reqedit,lev:u.lev?u.lev.limit:0,codes:!!u.codes,cl:u.codes?(u.codeLimit||0):0,qm:!!u.qmod}};
const dn=u=>u.display||u.name;
const specState=bt=>({t:'spec',p:bt.p.map(c=>pub(c.u)),chain:bt.chain,lives:bt.lives,turn:bt.turn,live:bt.live});
const me=c=>({...pub(c.u),bal:c.u.bal,mult:c.u.mult,account:!!c.acct,lim:c.u.lim||[],themes:c.u.owner?['rainbow']:(c.u.themes||[]),creq:(db.clans[c.u.creq]||{}).name||''});
function lobby(){const l=[...online.values()].map(c=>({...pub(c.u),busy:!!c.bt,away:!!c.inact,endless:!!c.end,party:!!c.plob,acct:!!c.acct}));for(const c of online.values())send(c,{t:'lobby',list:l,ownerTag:db.ownerTag})}
const addXp=(c,n)=>{if(!c.u.owner){c.u.xp+=n;c.u.bal+=n;gain(c.u,n)}if(c.acct)save();send(c,{t:'me',me:me(c)})};
const flash=(c,text,kind)=>send(c,{t:'flash',text,kind});
function login(c,u,acct){if(c.u)logout(c);c.u=u;if(acct)track(c,u);c.acct=acct;c.lastAct=Date.now();c.inact=false;c.hiddenSince=0;online.set(u.name.toLowerCase(),c);send(c,limMsg());send(c,{t:'me',me:me(c),colors:COLORS,shop:SHOP});lobby();if(poll&&!poll.done)sendPoll(c);onLogin(c)}
function logout(c){if(c.u&&c.acct)c.u.seen=Date.now();if(c.end)finishEnd(c,false);if(c.party)ptLeave(c);c.plob=false;if(c.watch){c.watch.spec.delete(c);c.watch=null}if(c.pend){clearTimeout(c.pend.tm);c.pend=null}if(c.u)online.delete(c.u.name.toLowerCase());end(c,false);c.u=null;lobby()}
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
function start(a,b){const bt={p:[a,b],lives:[3,3],chain:[],turn:0,live:false,t0:Date.now(),hist:[],spec:new Set()};[a,b].forEach(x=>{if(x.watch){x.watch.spec.delete(x);x.watch=null}});a.bt=b.bt=bt;
 bt.p.forEach((c,i)=>send(c,{t:'countdown',opp:pub(bt.p[1-i].u)}));lobby();
 setTimeout(()=>{if(a.bt===bt){bt.live=true;reset(bt,Math.round(Math.random()))}},4200)}
function reset(bt,turn){bt.chain=[WORDS[Math.random()*WORDS.length|0]];bt.turn=turn;bt.hist.push({k:'r',w:bt.chain[0]});push(bt)}
const BTIDLE=+process.env.BT_IDLE_MS||60000;
function idleWatch(bt){clearTimeout(bt.itm);clearTimeout(bt.iwarn);if(!bt.live)return;const cur=bt.p[bt.turn];if(!cur)return;
 bt.iwarn=setTimeout(()=>{if(cur.bt===bt&&bt.p[bt.turn]===cur)flash(cur,'⏳ Make a move or you will be kicked for inactivity!','warn')},Math.round(BTIDLE*.6));
 bt.itm=setTimeout(()=>{if(cur.bt!==bt||bt.p[bt.turn]!==cur)return;bt.why='inactive';const o=bt.p[1-bt.p.indexOf(cur)];flash(cur,'You were kicked for being inactive.','bad');if(o)flash(o,dn(cur.u)+' was inactive and got kicked. You win!');end(cur,false)},BTIDLE)}
function push(bt){idleWatch(bt);bt.p.forEach((c,i)=>send(c,{t:'battle',opp:pub(bt.p[1-i].u),chain:bt.chain,lives:bt.lives,you:i,turn:bt.turn}));bt.spec.forEach(s=>send(s,specState(bt)))}
function end(c,won){const bt=c.bt;if(!bt)return;clearTimeout(bt.itm);clearTimeout(bt.iwarn);const i=bt.p.indexOf(c),o=bt.p[1-i];bt.p.forEach(x=>{x.bt=null});
 const w=won?c:o;{const secs=Math.round((Date.now()-(bt.t0||Date.now()))/1000);for(const x of bt.p)if(x.u){const op=x===c?o:c;logGame(x.u,{k:'battle',res:x===w?'win':'loss',opp:op&&op.u?dn(op.u):'?',words:bt.chain.length,secs,xp:x===w&&!x.u.owner?Math.round(100*x.u.mult):0,why:bt.why||'',hist:bt.hist,names:bt.p.map(q=>q.u?dn(q.u):'?'),me:bt.p.indexOf(x)})}}bt.spec.forEach(s=>{s.watch=null;send(s,{t:'specover',winner:w.u?dn(w.u):'?'})});bt.spec.clear();if(w.u){addXp(w,Math.round(100*w.u.mult));qProg(w,'win');send(w,{t:'over',win:true});send(w===c?o:c,{t:'over',win:false})}lobby()}
function strike(c){c.strikes=(c.strikes||0)+1;if(c.strikes>=3){bans[c.ip]=Date.now()+6e5;send(c,{t:'banned'});c.ws.close()}
 else flash(c,c.strikes==2?'⚠ FINAL WARNING: keep it up and you will be banned.':'⚠ Warning: that word is not allowed.','warn')}
async function submit(c,w){const bt=c.bt;if(!bt||!bt.live||bt.p[bt.turn]!==c||bt.busy)return;
 w=String(w).toLowerCase().trim();if(!/^[a-z]{2,20}$/.test(w))return flash(c,'One word, letters only');
 if(filter.check(w)){flash(c,'That word does not count.','bad');return strike(c)}
 bt.busy=true;const ok=!bt.chain.includes(w)&&await rel(bt.chain.at(-1),w);bt.busy=false;if(!c.bt)return;
 const i=bt.p.indexOf(c);
 if(ok){bt.hist.push({k:'w',w,by:i});bt.chain.push(w);bt.turn=1-i;addXp(c,Math.round(10*c.u.mult));push(bt);return}
 flash(c,'That is unrelated!','bad');bt.spec.forEach(s=>send(s,{t:'specmsg',text:dn(c.u)+' said "'+w+'" - unrelated!'}));bt.lives[i]--;bt.hist.push({k:'x',w,by:i,lives:bt.lives[i]});
 if(bt.lives[i]<=0)return end(bt.p[1-i],true);reset(bt,1-i)}
const find=n=>online.get(String(n).toLowerCase());
function target(n){const c=find(n);if(c)return{c,u:c.u};const u=Object.values(db.users).find(x=>x.name.toLowerCase()==String(n).toLowerCase());return u&&{u}}
const okName=n=>/^[A-Za-z0-9_]{3,16}$/.test(n)&&!filter.check(n);
const TZ=process.env.TZ_NAME||'America/New_York',IDLE=+process.env.IDLE_MS||33*60000,HID=+process.env.HIDDEN_MS||60000,TICK=+process.env.TICK_MS||15000;
const ymd=()=>new Date().toLocaleDateString('en-CA',{timeZone:TZ});
function wk(d){const t=new Date(d+'T00:00:00Z');t.setUTCDate(t.getUTCDate()-(t.getUTCDay()+6)%7);return t.toISOString().slice(0,10)}
function roll(u){const d=ymd(),w=wk(d),m=d.slice(0,7),g=u.g=u.g||{d,dx:0,w,wx:0,m,mx:0};if(g.d!==d){g.d=d;g.dx=0}if(g.w!==w){g.w=w;g.wx=0}if(g.m!==m){g.m=m;g.mx=0}return g}
const gain=(u,n)=>{if(!n||u.owner||db.users[u.name]!==u)return;const g=roll(u);g.dx=Math.max(0,g.dx+n);g.wx=Math.max(0,g.wx+n);g.mx=Math.max(0,g.mx+n);qXp(u)};
const LBF={day:u=>u.owner?0:roll(u).dx,week:u=>u.owner?0:roll(u).wx,month:u=>u.owner?0:roll(u).mx,all:u=>u.owner?0:u.xp,time:u=>u.secs||0};
function rankOf(u){const us=Object.values(db.users),r={};for(const k in LBF){const v=LBF[k](u);r[k]={v:Math.round(v),rank:v>0?us.filter(x=>LBF[k](x)>v).length+1:0}}return r}
function friendLb(u){const us=[u,...(u.friends||[]).map(n=>db.users[n]).filter(Boolean)],o={};for(const k in LBF)o[k]=us.map(x=>({...pub(x),v:Math.round(LBF[k](x))})).sort((a,b)=>b.v-a.v);return o}
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
function onLogin(c){sendRaffles(c);const un=(c.u.inbox||[]).filter(x=>!x.read).length;if(un)send(c,{t:'inbox',unread:un,new:'📬 You have '+un+' new inbox message'+(un>1?'s':'')});if(canView(c))send(c,{t:'modreqs',list:reqList()});if(c.u.owner)send(c,{t:'ideas',list:ideaList()});if(c.acct){pushRooms([c.u.name]);pushFriends([c.u.name])}if(isMod(c))send(c,{t:'reports',list:reportList(c)});if(c.u.lev)send(c,liveStatus(c))}
let poll=null,pollT,pollBc;
const pkey=c=>c.u.name.toLowerCase();
function pview(own){const counts=poll.opts.map(()=>0);Object.values(poll.votes).forEach(i=>counts[i]++);return{id:poll.id,q:poll.q,opts:poll.opts,counts,total:Object.keys(poll.votes).length,ms:Math.max(0,poll.endsAt-Date.now()),done:poll.done,by:poll.by,...(own&&poll.done?{endedBy:poll.endedBy||''}:{})}}
function sendPoll(c){if(!poll||!c.u)return;send(c,{t:'poll',poll:pview(!!c.u.owner),mine:poll.votes[pkey(c)]})}
function bcPoll(){for(const x of online.values())sendPoll(x)}
function endPoll(){if(!poll||poll.done)return;poll.done=true;clearTimeout(pollT);bcPoll()}
const ENDCAP=500,ENDWORD=5,ENDBONUS=5,startWord=()=>WORDS[Math.random()*WORDS.length|0];
const esend=(c,msg)=>{const e=c.end;send(c,{t:'end',chain:e.chain,words:e.words,streak:e.streak,turn:e.turn,msg})};
const addEnd=(e,n)=>{e.xp=Math.min(ENDCAP,e.xp+n)};
function eh(e,ev){e.hist=e.hist||[];if(!e.hist.length)e.hist.push({k:'r',w:e.chain[0]});if(e.hist.length<400)e.hist.push(ev)}
function finishEnd(c,notify){const e=c.end;if(!e)return;c.end=null;const amt=Math.round(e.xp*c.u.mult);if(amt>0)addXp(c,amt);if(e.words>0||amt>0)logGame(c.u,{k:'endless',words:e.words,best:e.best,xp:amt,hist:e.hist||[]});
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
 if(!pick){qProg(c,'stump');addEnd(e,ENDBONUS);eh(e,{k:'s'});e.chain=[startWord()];e.hist.push({k:'r',w:e.chain[0]});e.streak=0;e.turn='you';return esend(c,'🤖 The bot is stumped and could not find a word! +'+ENDBONUS+' bonus XP. New word!')}
 eh(e,{k:'w',w:pick,by:'bot'});e.chain.push(pick);e.turn='you';esend(c,'🤖 The bot said "'+pick+'"')}
const fuser=n=>db.users[acctName(n)||''];
const hasF=(u,n)=>(u.friends||[]).some(x=>lc(x)==lc(n));
const friendView=u=>{const v=n=>({name:n,dn:dn(db.users[n]||{name:n})});return{friends:(u.friends||[]).map(v),inc:(u.fin||[]).map(v),out:(u.fout||[]).slice()}};
function pushFriends(names){for(const x of online.values())if(x.acct&&x.u&&names.some(n=>lc(n)==lc(x.u.name)))send(x,{t:'friends',...friendView(x.u)})}
function makeFriends(a,b){for(const[u,o]of[[a,b],[b,a]]){u.friends=u.friends||[];if(!hasF(u,o.name))u.friends.push(o.name);u.fin=(u.fin||[]).filter(x=>lc(x)!=lc(o.name));u.fout=(u.fout||[]).filter(x=>lc(x)!=lc(o.name))}}
const evLeft=u=>u.lev?Math.max(0,u.lev.limit-(u.evUsed&&u.evUsed.d===ymd()?u.evUsed.n:0)):0;
const liveStatus=c=>({t:'liveev',on:!!c.u.lev,limit:c.u.lev?c.u.lev.limit:0,left:evLeft(c.u)});
let evt=null,evtCool=0;const evPend=new Map();const EV_START=4000,EV_DUR=15000,EV_COST=10000,BH_START=6800,BH_SPAN=3500,ST_START=1500,ST_SPAN=20500,TK_START=10600,TK_SPAN=27000;
function startEvent(by,kind){const bh=kind==='blackhole',st=kind==='stampede',tk=kind==='turkey',startIn=bh?BH_START:st?ST_START:tk?TK_START:EV_START,span=bh?BH_SPAN:st?ST_SPAN:tk?TK_SPAN:EV_DUR,coins=[];let t=0,id=0;
 while(t<span){const big=Math.random()<(st?0.4:tk?0.22:0.08);coins.push({id:id++,t:Math.round(t),big,x:5+Math.random()*88,y:st?18+Math.random()*72:14+Math.random()*78,life:st?3000:tk?3200:bh?(big?6500:7500):(big?2800:3500)});t+=st?190+Math.random()*100:tk?230+Math.random()*120:(bh?50:170)+Math.random()*(bh?40:90)}
 if(tk){for(let i=0;i<8;i++)coins.push({id:id++,t:Math.round(Math.max(400,(i+.5)*span/8+(Math.random()-.5)*1800)),big:false,inv:true,x:8+Math.random()*82,y:20+Math.random()*66,life:3000});for(let i=0;i<5;i++)coins.push({id:id++,t:Math.round(1500+(i+Math.random())*(span-3000)/5),big:true,mega:true,x:10+Math.random()*75,y:18+Math.random()*60,life:3400})}
 if(st)for(let i=0;i<6;i++)coins.push({id:id++,t:Math.round(Math.max(600,(i+.5)*span/6+(Math.random()-.5)*1400)),big:false,inv:true,x:8+Math.random()*82,y:20+Math.random()*66,life:2800});
 let nb=coins.filter(c=>c.big).length;while(nb<(st?24:tk?0:4)){const c=coins[Math.random()*coins.length|0];if(!c.big){c.big=true;c.life=bh?6500:st?3000:2800;nb++}}
 const e=evt={id:Date.now(),coinsAt:Date.now()+startIn,coins:new Map(coins.map(c=>[c.id,c])),claims:{}};const total=startIn+span+(bh?7500:st?3000:tk?3400:3500)+1000;evtCool=Date.now()+total+60000;
 const msg={t:'tevent',kind:bh?'blackhole':st?'stampede':tk?'turkey':'token',by:dn(by),id:e.id,startIn,coins};for(const x of online.values())send(x,msg);
 setTimeout(()=>{if(evt===e)evt=null},total)}
const RCATS=['player','name','chat','bug','other'];
const reportList=c=>db.reports.slice(-100).filter(r=>c.u.owner||!r.tmod).map(r=>({id:r.id,by:r.by,byDn:r.byDn,target:r.target,tdn:r.tdn,cat:r.cat,text:r.text,ctx:r.ctx,at:r.at,status:r.status}));
const pushReports=()=>{for(const x of online.values())if(isMod(x))send(x,{t:'reports',list:reportList(x)})};
const isMod=c=>c.u&&c.acct&&(c.u.owner||c.u.mod);
const canAnn=c=>c.u&&c.acct&&(c.u.owner||c.u.mod||c.u.alpha);
const canHit=(c,u)=>u!==c.u&&!u.owner&&(c.u.owner||!u.mod);

const pushCal=()=>{for(const x of online.values())send(x,{t:'cal',list:db.calendar})};
/* ---- daily quests ---- */
const QT={stump:n=>`Stump the Endless bot ${n}x`,win:n=>`Beat ${n} player${n>1?'s':''} in battle`,mpwin:n=>`Win ${n} Multiplayer game${n>1?'s':''}`,mega:n=>`Play in ${n} Mega Lobb${n>1?'ies':'y'}`,raffle:n=>`Enter ${n} raffle${n>1?'s':''}`,event:n=>`Collect ${n} live-event token${n>1?'s':''}`,abuse:n=>`Participate in ${n} admin abuse${n>1?'s':''}`,xp:n=>`Earn ${n} XP today`};
const QABUSE=['mega','raffle','event'],canQ=c=>!!(c.acct&&c.u&&(c.u.owner||c.u.qmod));
const qTitle=q=>q.title||QT[q.type](q.target);
function qDay(u){const d=ymd();if(!u.qd||u.qd.d!==d)u.qd={d,p:{},c:[]};return u.qd}
const qMine=(u,q)=>q.byu?q.byu===u.name:q.by===dn(u);
const qDone=(u,q)=>qMine(u,q)?0:q.type==='xp'?(u.owner?0:roll(u).dx):(qDay(u).p[q.id]||0);
function qView(c){const u=c.u,ed=canQ(c),pl=!!(c.acct&&u&&!u.owner),d=pl?qDay(u):null;
 return{t:'quests',edit:ed,play:pl,types:Object.keys(QT),list:db.quests.filter(q=>q.on||ed).map(q=>{const pr=pl?Math.min(q.target,qDone(u,q)):0;return{id:q.id,type:q.type,target:q.target,title:qTitle(q),custom:q.title||'',on:q.on,reward:q.reward,rt:rwText(q.reward),prog:pr,done:pl&&pr>=q.target,claimed:!!(d&&d.c.includes(q.id)),mine:pl&&qMine(u,q),...(ed?{n:qCnt(q.id)}:{})}})}}
function qSend(c){if(!c.u)return;if(Date.now()-(c.qAt||0)<250){clearTimeout(c.qT);c.qT=setTimeout(()=>{c.qAt=0;qSend(c)},260);return}c.qAt=Date.now();send(c,qView(c))}
function qProg(c,type,n){if(!c||!c.acct||!c.u||c.u.owner||!db.quests.length)return;const d=qDay(c.u),fin=[];
 for(const q of db.quests){if(!q.on||q.type==='xp'||qMine(c.u,q))continue;if(!(q.type===type||(q.type==='abuse'&&QABUSE.includes(type))))continue;const was=d.p[q.id]||0;if(was>=q.target)continue;d.p[q.id]=Math.min(q.target,was+(n||1));if(d.p[q.id]>=q.target)fin.push(q)}
 if(fin.length){fin.forEach(q=>qLogDone(c.u,q));save();fin.forEach(q=>flash(c,'📜 Quest complete: '+qTitle(q)+' — claim your reward!','ok'))}qSend(c)}
const qCnt=(id)=>Object.keys(((db.qlog||{})[ymd()]||{})[id]||{}).length;
function qLogDone(u,q){db.qlog=db.qlog||{};const day=ymd(),L=db.qlog[day]=db.qlog[day]||{},m=L[q.id]=L[q.id]||{};if(!m[u.name])m[u.name]={at:Date.now()};const ks=Object.keys(db.qlog).sort();while(ks.length>14)delete db.qlog[ks.shift()]}
function qXp(u){if(!db.quests||!db.quests.length||u.owner)return;for(const q of db.quests){if(!q.on||q.type!=='xp'||qMine(u,q))continue;const m=((db.qlog||{})[ymd()]||{})[q.id];if(m&&m[u.name])continue;if(roll(u).dx>=q.target){qLogDone(u,q);const c=find(u.name);if(c&&c.u===u){flash(c,'📜 Quest complete: '+qTitle(q)+' — claim your reward!','ok');qSend(c)}}}}
function logGame(u,e){if(!u)return;if(e.hist&&e.hist.length>150)e.hist=e.hist.slice(-150);u.log=u.log||[];u.log.unshift({at:Date.now(),...e});if(u.log.length>100)u.log.length=100;for(let i=25;i<u.log.length;i++)delete u.log[i].hist;if(db.users[u.name]===u)save()}
const pushQuests=()=>{for(const x of online.values())if(x.u){x.qAt=0;send(x,qView(x))}};
/* ---- clans ---- */
const CLANMAX=5,clanKey=n=>lc(n),RESERVED=/^(owner|admin|mod|staff|system)$/i;
const clanOf=u=>u&&u.clan&&db.clans[u.clan]||null,clanTagOf=u=>{const c=clanOf(u);return c?c.name:''};
const clanMembers=c=>c.members.map(n=>db.users[n]).filter(Boolean);
const clanTotal=(c,k)=>clanMembers(c).reduce((a,u)=>a+Math.max(0,LBF[k||'all'](u)),0);
function clanView(c,viewer){const vu=viewer&&viewer.u,key=clanKey(c.name),mine=!!(vu&&vu.clan==key),isL=mine&&lc(vu.name)==lc(c.leader);
 return{t:'clanview',name:c.name,leader:c.leader,leaderDn:dn(db.users[c.leader]||{name:c.leader}),max:CLANMAX,total:Math.round(clanTotal(c)),
  members:clanMembers(c).map(u=>({...pub(u),v:Math.round(u.owner?0:u.xp||0),lead:lc(u.name)==lc(c.leader)})).sort((a,b)=>b.lead-a.lead||b.v-a.v),
  mine,isLeader:isL,reqs:isL?c.req.map(n=>db.users[n]).filter(Boolean).map(pub):[],pending:!!(vu&&vu.creq==key),canJoin:!!(vu&&viewer.acct&&!vu.clan&&!vu.creq&&c.members.length<CLANMAX)}}
function clanSelf(x){if(x&&x.u)send(x,{t:'clanme',clan:clanTagOf(x.u),creq:(db.clans[x.u.creq]||{}).name||''})}
function clanPush(c){for(const n of c.members){const x=find(n);if(x&&x.acct)send(x,clanView(c,x))}}
function clanDisband(c){for(const n of c.members){const u=db.users[n];if(u)u.clan=''}for(const n of c.req){const u=db.users[n];if(u&&u.creq==clanKey(c.name))u.creq=''}delete db.clans[clanKey(c.name)]}
function clanDrop(u){if(u.creq){const c0=db.clans[u.creq];if(c0)c0.req=c0.req.filter(n=>lc(n)!=lc(u.name));u.creq=''}
 const key=u.clan;if(!key)return null;const c=db.clans[key];u.clan='';if(!c)return null;c.members=c.members.filter(n=>lc(n)!=lc(u.name));
 if(!c.members.length){clanDisband(c);return null}if(lc(c.leader)==lc(u.name))c.leader=c.members[0];return c}
function clanBoards(){const cs=Object.values(db.clans),o={};for(const k in LBF)o[k]=cs.map(c=>({name:c.name,n:c.members.length,v:Math.round(clanTotal(c,k))})).sort((a,b)=>b.v-a.v||a.name.localeCompare(b.name)).slice(0,50);return o}
/* ---- device tracking, linked bans, account manager ---- */
const DEVRE=/^[a-f0-9]{16,48}$/;
function track(c,u){if(db.users[u.name]!==u)return;u.seen=Date.now();if(c.dev){u.devs=u.devs||[];if(!u.devs.includes(c.dev)){u.devs.push(c.dev);if(u.devs.length>12)u.devs.shift()}}
 if(c.ip){u.ips=u.ips||[];if(!u.ips.includes(c.ip)){u.ips.push(c.ip);if(u.ips.length>12)u.ips.shift()}}}
const ownerDev=d=>Object.values(db.users).some(u=>u.owner&&(u.devs||[]).includes(d));
function linkedOf(u){const names=new Set([u.name]),devs=new Set((u.devs||[]).filter(d=>!ownerDev(d)));let grew=true;
 while(grew){grew=false;for(const x of Object.values(db.users)){if(x.owner||names.has(x.name))continue;if((x.devs||[]).some(d=>devs.has(d))){names.add(x.name);(x.devs||[]).forEach(d=>{if(!ownerDev(d))devs.add(d)});grew=true}}}
 return{users:[...names].map(n=>db.users[n]).filter(Boolean),devs:[...devs]}}
function kickName(n,b){const o=find(n);if(o){send(o,banMsg(b));setTimeout(()=>o.ws.close(),300)}}
function banAcct(u,reason,by,mins){const b={until:mins?Date.now()+mins*6e4:0,reason:String(reason||'').slice(0,80),by};db.bans[lc(u.name)]=b;kickName(u.name,b);return b}
function terminateAcct(u,reason,by){clanDrop(u);const n=u.name,b={until:0,reason:String(reason||'Account terminated').slice(0,80),by};db.bans[lc(n)]=b;kickName(n,b);
 delete db.users[n];for(const t of Object.keys(db.tokens))if(db.tokens[t]===n)delete db.tokens[t];
 for(const x of Object.values(db.users)){for(const k of['friends','fin','fout'])if(x[k])x[k]=x[k].filter(y=>lc(y)!=lc(n))}}
function devGate(c,n){const d=c.dev&&db.devbans[c.dev];if(!d)return false;if(d.until&&d.until<Date.now()){delete db.devbans[c.dev];save();return false}
 const k=n&&acctName(n),u=k&&db.users[k];if(u&&u.owner)return false;
 const b={until:d.until||0,reason:d.reason||'Banned device',by:'system'};
 if(u){if(d.term)terminateAcct(u,'Banned device','system');else db.bans[lc(u.name)]=b;save()}
 send(c,banMsg(b));setTimeout(()=>c.ws.close(),300);return true}
function acctRow(u){return{name:u.name,dn:dn(u),xp:u.xp||0,online:!!find(u.name),seen:u.seen||0,banned:!!banInfo(u.name),mod:!!u.mod,owner:!!u.owner}}
function acctDetail(u){const lk=linkedOf(u),ips=(u.ips||[]).map(ip=>({ip,shared:Object.values(db.users).filter(x=>x!==u&&(x.ips||[]).includes(ip)).map(x=>x.name).slice(0,10)})),
 devs=(u.devs||[]).map(d=>({id:d.slice(0,8),banned:!!db.devbans[d],owner:ownerDev(d),shared:Object.values(db.users).filter(x=>x!==u&&(x.devs||[]).includes(d)).map(x=>x.name).slice(0,10)}));
 const b=banInfo(u.name);return{...acctRow(u),clan:clanTagOf(u),bal:u.bal||0,mult:u.mult||1,color:u.color,tag:u.tag||'',alpha:!!u.alpha,codes:!!u.codes,secs:u.secs||0,born:u.born||0,friends:(u.friends||[]).length,
  ban:b?{until:b.until,reason:b.reason,by:b.by}:null,devs,ips,linked:lk.users.filter(x=>x!==u).map(x=>({name:x.name,banned:!!banInfo(x.name)}))}}
const banInfo=n=>{const k=String(n||'').toLowerCase(),b=db.bans[k];if(!b)return null;if(b.until&&b.until<Date.now()){delete db.bans[k];save();return null}return b};
const banMsg=b=>({t:'banned',manual:true,reason:b.reason||'',until:b.until||0});
const blocked=(c,n)=>{const b=banInfo(n);if(!b)return false;send(c,banMsg(b));setTimeout(()=>c.ws.close(),300);return true};
// ===== Multiplayer (party) mode: up to 6 players, host starts, 3 lives each, last one standing wins =====
const parties=new Map(),PMAX=6,PLIVES=3,PTURN=30000;
const ptCode=()=>{const A='ABCDEFGHJKLMNPQRSTUVWXYZ23456789';let s;do{s='';for(let i=0;i<5;i++)s+=A[crypto.randomInt(A.length)]}while([...parties.values()].some(p=>p.code===s));return s};
const ptList=()=>[...parties.values()].filter(p=>!p.priv&&p.state==='lobby'&&!p.done).map(p=>({id:p.id,host:pub(p.host.u),count:ptCount(p),max:p.max,mega:!!p.mega,name:p.name||'',rw:p.reward||null}));
function ptSendList(){const l=ptList();for(const x of online.values())if(x.plob&&!x.party)send(x,{t:'plist',list:l})}
function ptPush(p){const cur=p.state==='playing'?p.m[p.turn]:null;
 const o={t:'party',id:p.id,priv:p.priv,code:p.priv?p.code:'',host:p.host.u.name,max:p.max,mega:!!p.mega,mname:p.name||'',reward:p.reward||null,done:!!p.done,state:p.state,
  members:p.m.map(x=>({...pub(x.u),lives:x.lives,out:!!x.out,left:!!x.left,spec:!!x.spec})),chain:p.chain,turn:cur?cur.u.name:'',
  ms:cur?Math.max(0,p.deadline-Date.now()):0,msg:p.msg||'',result:p.result||null};
 for(const x of p.m)if(!x.left)send(x.c,o)}
function ptDelete(p){clearTimeout(p.tm);p.tok++;parties.delete(p.id);ptSendList()}
const ptNext=(p,i)=>{const n=p.m.length;for(let k=1;k<=n;k++){const j=(i+k)%n;if(!p.m[j].out)return j}return i};
function ptTimer(p){clearTimeout(p.tm);const tok=++p.tok;p.deadline=Date.now()+PTURN;
 p.tm=setTimeout(()=>{if(p.state!=='playing'||p.tok!==tok)return;const cur=p.m[p.turn];if(cur)ptLose(p,cur,dn(cur.u)+' ran out of time!')},PTURN)}
const PTXP={2:100,3:300,4:400,5:500};const ptWin=n=>n>=6?650:(PTXP[n]||100);
function ptStartGame(p){p.n=p.m.filter(x=>!x.spec).length;p.state='playing';p.result=null;p.msg='';p.m.forEach(x=>{x.lives=PLIVES;x.out=!!x.spec});p.chain=[startWord()];p.hist=[{k:'r',w:p.chain[0]}];{const al=p.m.map((x,i)=>i).filter(i=>!p.m[i].out);p.turn=al[Math.random()*al.length|0]}ptTimer(p);ptPush(p);ptSendList();lobby()}
function ptFinish(p,w){clearTimeout(p.tm);p.tok++;p.state='lobby';let xp=0;
 let rw=null;
 if(w&&!w.left&&w.c.u&&!w.spec){qProg(w.c,'mpwin');if(p.reward){rw=p.reward;giveReward(w.u.name,rw)}else{xp=Math.round(ptWin(p.n||2)*w.u.mult);addXp(w.c,xp)}}
 if(p.mega)p.done=true;
 {const pl=p.m.filter(x=>!x.spec&&x.u);for(const x of pl)logGame(x.u,{k:'party',mega:!!p.mega,name:p.name||'',res:x===w?'win':w?'loss':'draw',players:pl.length,xp:x===w?xp:0,rw:x===w&&rw?rwText(rw):'',hist:p.hist||[],names:pl.map(q=>dn(q.u)),me:dn(x.u)})}
 p.result={winner:w?dn(w.u):null,name:w?w.u.name:'',xp:w&&!w.u.owner?xp:0,reward:rw,msg:p.msg||''};
 if(rw&&w)for(const y of online.values())send(y,{t:'announce',text:'🏆 '+dn(w.u)+' won the Mega Lobby and got '+rwText(rw)+'!',from:'Mega Lobby'});
 p.m=p.m.filter(x=>!x.left);if(!p.m.length)return ptDelete(p);
 if(!p.m.includes(p.host))p.host=p.m[0];
 p.chain=[];ptPush(p);ptSendList();lobby()}
function ptLose(p,cur,msg){cur.lives--;if(cur.lives<=0)cur.out=true;p.hist.push({k:'x',by:dn(cur.u),msg,lives:cur.lives,out:!!cur.out});p.msg=msg+(cur.out?' ☠ Eliminated!':'');
 const live=p.m.filter(x=>!x.out);if(live.length<=1)return ptFinish(p,live[0]||null);
 p.chain=[startWord()];p.hist.push({k:'r',w:p.chain[0]});p.turn=ptNext(p,p.turn);ptTimer(p);ptPush(p)}
function ptLeave(c){const p=c.party;if(!p)return;c.party=null;const i=p.m.findIndex(x=>x.c===c);if(i<0)return;const x=p.m[i];
 if(p.state==='playing'){x.left=true;x.out=true;
  if(!p.m.some(y=>!y.left))return ptDelete(p);
  if(p.host===x)p.host=p.m.find(y=>!y.left);
  const live=p.m.filter(y=>!y.out);
  if(live.length<=1){p.msg=dn(x.u)+' left the game';return ptFinish(p,live[0]||null)}
  p.msg=dn(x.u)+' left the game';if(p.m[p.turn]===x){p.turn=ptNext(p,p.turn);ptTimer(p)}ptPush(p)}
 else{if(p.mega&&p.host===x){for(const y of p.m)if(y!==x){y.c.party=null;send(y.c,{t:'pgone'});flash(y.c,'The Mega Lobby was closed by the host','warn')}return ptDelete(p)}
  p.m.splice(i,1);if(!p.m.length)return ptDelete(p);if(p.host===x)p.host=p.m[0];ptPush(p)}
 ptSendList()}
async function ptSubmit(c,w){const p=c.party;if(!p||p.state!=='playing')return;const cur=p.m[p.turn];if(!cur||cur.c!==c||cur.busy)return;
 w=String(w).toLowerCase().trim();if(!/^[a-z]{2,20}$/.test(w))return flash(c,'One word, letters only');
 if(filter.check(w)){flash(c,'That word does not count.','bad');return strike(c)}
 const tok=p.tok;cur.busy=true;let ok=false;try{ok=!p.chain.includes(w)&&await rel(p.chain.at(-1),w)}finally{cur.busy=false}
 if(p.state!=='playing'||p.tok!==tok||p.m[p.turn]!==cur||c.party!==p)return;
 if(ok){p.hist.push({k:'w',w,by:dn(cur.u)});p.chain.push(w);p.msg='';addXp(c,Math.round(10*c.u.mult));p.turn=ptNext(p,p.turn);ptTimer(p);return ptPush(p)}
 flash(c,'That is unrelated!','bad');ptLose(p,cur,dn(cur.u)+' said "'+w+'" - unrelated!')}
// ===== Limited colors, rewards, Mega Lobby helpers, Raffles =====
const LIMSEED=[
 {id:'l_goldenhaze',name:'Golden Haze',kind:'gradient',anim:'shine',speed:1,stops:['#b8860b','#ffd700']},
 {id:'l_bluehaze',name:'Blue Haze',kind:'gradient',anim:'none',speed:1,stops:['#2563eb','#06b6d4','#10b981']},
 {id:'l_firerampage',name:'Fire Rampage',kind:'gradient',anim:'flow',speed:1,stops:['#dc2626','#f97316','#facc15']},
 {id:'l_silverhaze',name:'Silver Haze',kind:'gradient',anim:'shine',speed:1,stops:['#4b5563','#9ca3af']}];
const LIMANIM=['none','flow','shine','pulse','flicker','hue'];
function limNorm(d){if(d.kind==='animated'){d.kind='gradient';d.anim='flow'}else if(d.kind==='shine'){d.kind='gradient';d.anim='shine'}if(!LIMANIM.includes(d.anim))d.anim='none';d.speed=Math.min(4,Math.max(.4,+d.speed||1))}
function limSeed(){db.limcolors=db.limcolors||{};if(!db.limSeeded){for(const d of LIMSEED)if(!db.limcolors[d.id])db.limcolors[d.id]=d;db.limSeeded=true}if(db.limcolors[THX_ID]&&!db.limcolors[THX_ID].glow)db.limcolors[THX_ID].glow='#f97316';
 if(!db.thxSeeded){if(!db.limcolors[THX_ID])db.limcolors[THX_ID]={id:THX_ID,name:'Harvest Feast',kind:'gradient',anim:'flow',speed:1,fx:'leaves',glow:'#f97316',stops:['#5c3317','#c0392b','#fff5e1','#e67e22','#7b3f00']};db.thx={end:Date.now()+THX_DAYS*864e5};db.thxSeeded=true;save()}
 Object.values(db.limcolors).forEach(limNorm)}
const hasLim=id=>typeof id==='string'&&Object.prototype.hasOwnProperty.call(db.limcolors,id);
const ownsLim=(u,id)=>hasLim(id)&&!!(u.owner||(u.lim||[]).includes(id));
const thxOn=()=>!!(db.thx&&Date.now()<db.thx.end&&hasLim(THX_ID));
const shopMsg=()=>({t:'shop',now:Date.now(),mult:SHOP,thx:thxOn()?{id:THX_ID,end:db.thx.end,price:THX_PRICE}:null,rb:RB_PRICE,cols:Object.values(db.limcolors).filter(d=>d.id!==THX_ID&&d.price>0).map(d=>({id:d.id,price:d.price}))});
const limMsg=()=>({t:'limdefs',defs:db.limcolors});
const pushLim=()=>{const m=limMsg();for(const x of online.values())send(x,m)};
const ptCount=p=>p.m.filter(x=>!x.spec&&!x.left).length;
function rwNorm(r){r=r&&typeof r==='object'?r:{};const xp=Math.max(0,Math.min(1e9,Math.floor(+r.xp)||0)),color=hasLim(r.color)?r.color:'',mult=(+r.mult===1.5||+r.mult===2)?+r.mult:0;return(xp||color||mult)?{xp,color,mult}:null}
const rwText=r=>[r.xp?r.xp.toLocaleString('en-US')+' XP':'',r.color&&hasLim(r.color)?db.limcolors[r.color].name:'',r.mult?r.mult+'x XP multiplier':''].filter(Boolean).join(' + ')||'a surprise';
function giveReward(name,r){const k=acctName(name),u=k&&db.users[k];if(!u||u.owner||!r)return false;
 if(r.xp){u.xp+=r.xp;u.bal+=r.xp;gain(u,r.xp)}
 if(r.color&&hasLim(r.color)){u.lim=u.lim||[];if(!u.lim.includes(r.color))u.lim.push(r.color)}
 if(r.mult&&r.mult>u.mult)u.mult=r.mult;
 save();const c=find(u.name);if(c&&c.u===u)send(c,{t:'me',me:me(c)});return true}
const pubN=n=>db.users[n]?pub(db.users[n]):{name:n,dn:n,color:'white',xp:0};
// ---- raffles ----
const rtim=new Map();let rpT=0;
function schedR(r){clearTimeout(rtim.get(r.id));rtim.set(r.id,setTimeout(()=>drawRaffle(r.id),Math.min(2147483000,Math.max(0,r.endsAt-Date.now()))))}
const raffleList=c=>{const now=Date.now();return db.raffles.filter(r=>!r.done||now-(r.doneAt||0)<3*864e5).slice(-20).map(r=>({id:r.id,title:r.title,rw:r.reward,rwt:rwText(r.reward),winners:r.winners,ms:Math.max(0,r.endsAt-now),count:r.entries.length,mine:!!(c.u&&c.acct&&r.entries.includes(c.u.name)),done:r.done,win:r.done?r.win.map(pubN):[]}))};
const sendRaffles=c=>{if(c.u)send(c,{t:'raffles',list:raffleList(c)})};
const pushRafflesNow=()=>{clearTimeout(rpT);rpT=0;for(const x of online.values())sendRaffles(x)};
const pushRaffles=()=>{if(!rpT)rpT=setTimeout(()=>{rpT=0;for(const x of online.values())sendRaffles(x)},300)};
function drawRaffle(id){const r=db.raffles.find(x=>x.id===id);if(!r||r.done)return;if(Date.now()<r.endsAt-100)return schedR(r);
 r.done=true;r.doneAt=Date.now();rtim.delete(r.id);
 const pool=r.entries.filter(n=>db.users[n]&&!db.users[n].owner),win=[];
 while(win.length<r.winners&&pool.length)win.push(pool.splice(crypto.randomInt(pool.length),1)[0]);
 r.win=win;
 for(const n of win){giveReward(n,r.reward);inboxAdd(n,true,{kind:'raffle',text:'🎉 You won the raffle'+(r.title?' "'+r.title+'"':'')+'! Prize: '+rwText(r.reward)})}
 save();
 for(const x of online.values())send(x,{t:'rafflewin',id:r.id,title:r.title,rw:r.reward,win:win.map(pubN),entered:!!(x.u&&x.acct&&r.entries.includes(x.u.name)),count:r.entries.length});
 pushRafflesNow()}
// ===== Redeem codes =====
const CODE_MAXXP=1000,hasCode=k=>Object.prototype.hasOwnProperty.call(db.codes,k);
const canCode=c=>c.u&&c.acct&&(c.u.owner||c.u.codes);
const codeLeft=u=>u.codes?Math.max(0,(u.codeLimit||0)-(u.codeUsed&&u.codeUsed.d===ymd()?u.codeUsed.n:0)):0;
const codeWho=x=>x.used.slice(0,200).map(n=>({name:n,dn:dn(db.users[n]||{name:n}),at:((x.log||[]).find(l=>l.n===n)||{}).at||0}));
const codesMsg=c=>({t:'codes',owner:!!c.u.owner,limit:c.u.owner?0:(c.u.codeLimit||0),left:c.u.owner?0:codeLeft(c.u),list:Object.values(db.codes).filter(x=>c.u.owner||x.by===c.u.name).sort((a,b)=>b.at-a.at).slice(0,100).map(x=>({code:x.code,xp:x.xp,max:x.max,used:x.used.length,by:x.by,...(c.u.owner?{who:codeWho(x)}:{})}))});
const pushCodes=()=>{for(const x of online.values())if(canCode(x))send(x,codesMsg(x))};
const handlers={
 guest(c,m){const n=String(m.name||'');if(blocked(c,n))return;if(!okName(n))return flash(c,'Name: 3-16 letters/numbers/_','bad');
  if(find(n)||Object.keys(db.users).some(k=>k.toLowerCase()==n.toLowerCase()))return flash(c,'Username taken','bad');
  login(c,{name:n,xp:0,bal:0,mult:1,color:'white',tag:''},false)},
 signup(c,m){const n=String(m.name||'');if(blocked(c,n))return;if(!okName(n)||String(m.pass||'').length<6)return flash(c,'Valid name + password (6+ chars) needed','bad');
  if(find(n)&&find(n)!==c||Object.keys(db.users).some(k=>k.toLowerCase()==n.toLowerCase()))return flash(c,'Username taken','bad');
  const u=mk(n,m.pass);u.owner=false;u.born=Date.now();db.users[n]=u;const tk=crypto.randomBytes(24).toString('hex');db.tokens[tk]=n;save();login(c,u,true);send(c,{t:'token',tk})},
 login(c,m){if(blocked(c,m.name))return;const u=db.users[m.name];if(!u||hash(String(m.pass),u.salt)!==u.hash)return flash(c,'Wrong username or password','bad');
  const o=find(u.name);if(o&&o!==c){logout(o);o.ws.close()}
  const tk=crypto.randomBytes(24).toString('hex');db.tokens[tk]=u.name;save();login(c,u,true);send(c,{t:'token',tk})},
 resume(c,m){const n=db.tokens[m.tk],u=n&&db.users[n];if(!u)return send(c,{t:'badtoken'});if(blocked(c,n))return;const o=find(n);if(o&&o!==c){logout(o);o.ws.close()}login(c,u,true)},
 challenge(c,m){if(c.end)return flash(c,'Stop endless mode first','warn');const o=find(m.to);if(!o||o===c||o.bt||o.end||o.plob||c.plob||c.bt||c.pend)return;
  c.pend={to:o,tm:setTimeout(()=>{if(c.pend&&c.pend.to===o){c.pend=null;send(c,{t:'noresp',name:dn(o.u)});send(o,{t:'chalgone',from:c.u.name})}},20000)};
  send(o,{t:'challenge',from:c.u.name,dn:dn(c.u)})},
 deny(c,m){const o=find(m.from);if(!o||!o.pend||o.pend.to!==c)return;clearTimeout(o.pend.tm);o.pend=null;send(o,{t:'denied',name:dn(c.u)})},
 accept(c,m){if(c.end)return flash(c,'Stop endless mode first','warn');const o=find(m.from);if(!o||!o.pend||o.pend.to!==c||o.bt||c.bt||c.plob)return;clearTimeout(o.pend.tm);o.pend=null;start(o,c)},
 typing(c,m){const bt=c.bt;if(!bt)return;const txt=filter.clean(String(m.text).slice(0,24)),i=bt.p.indexOf(c);send(bt.p[1-i],{t:'opptype',text:txt});bt.spec.forEach(s=>send(s,{t:'spectype',who:i,text:txt}))},
 watch(c,m){const o=find(m.who);if(!o||!o.bt||c.bt||c.end||c.plob||c===o)return;if(c.watch)c.watch.spec.delete(c);c.watch=o.bt;o.bt.spec.add(c);send(c,specState(o.bt))},
 unwatch(c){if(c.watch){c.watch.spec.delete(c);c.watch=null}},
 setdisplay(c,m){const x=String(m.text||'').trim().replace(/\s+/g,' ');
  if(x){if(!/^[A-Za-z0-9_ .!-]{2,20}$/.test(x)||filter.check(x))return flash(c,'Display name: 2-20 letters, numbers, spaces, _ . ! - (no bad words)','bad');
   const lc=x.toLowerCase();if(lc!==c.u.name.toLowerCase()&&(Object.keys(db.users).some(k=>k.toLowerCase()==lc)||[...online.values()].some(o=>o!==c&&((o.u.display||'').toLowerCase()==lc||o.u.name.toLowerCase()==lc))))return flash(c,'That display name is taken','bad')}
  c.u.display=x;if(c.acct)save();send(c,{t:'me',me:me(c)});if(c.bt&&c.bt.live)push(c.bt);lobby()},
 submit(c,m){submit(c,m.word)},
 forfeit(c){if(!c.bt)return send(c,{t:'nobattle'});c.bt.why='forfeit';end(c,false)},
 codeslist(c){if(canCode(c))send(c,codesMsg(c))},
 codemake(c,m){if(!canCode(c))return;const own=c.u.owner,raw=String(m.code||'').trim();
  if(!/^[A-Za-z0-9_-]{3,20}$/.test(raw)||raw.toLowerCase()==='__proto__')return flash(c,'Code: 3-20 letters, numbers, _ or -','bad');
  const max=Math.floor(+m.max),xp=Math.floor(+m.xp);
  if(!(max>=1&&max<=100000))return flash(c,'People who can redeem: 1 to 100000','bad');
  if(!(xp>=1&&xp<=1e9))return flash(c,'XP must be at least 1','bad');
  if(!own&&xp>CODE_MAXXP)return flash(c,'You can give at most '+CODE_MAXXP+' XP per code','bad');
  if(!own&&Object.values(db.codes).filter(x=>x.by===c.u.name).length>=100)return flash(c,'You have too many codes. Delete some first.','bad');
  const k=raw.toLowerCase();if(hasCode(k))return flash(c,'That code already exists','bad');
  if(!own&&codeLeft(c.u)<=0)return flash(c,'You used all '+(c.u.codeLimit||0)+' of your codes for today. Try again tomorrow.','warn');
  if(!own){const d=ymd(),n=c.u.codeUsed&&c.u.codeUsed.d===d?c.u.codeUsed.n:0;c.u.codeUsed={d,n:n+1}}
  db.codes[k]={code:raw,xp,max,used:[],log:[],by:c.u.name,at:Date.now()};save();flash(c,'Code "'+raw+'" created','ok');pushCodes()},
 codedel(c,m){if(!canCode(c))return;const k=String(m.code||'').toLowerCase();if(!hasCode(k))return;const x=db.codes[k];if(!(c.u.owner||x.by===c.u.name))return;delete db.codes[k];save();pushCodes()},
 setcodes(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t||t.u.owner||db.users[t.u.name]!==t.u)return;if(m.on){t.u.codes=true;t.u.codeLimit=Math.max(1,Math.min(100,Math.floor(+m.limit)||5))}else{delete t.u.codes;delete t.u.codeLimit}save();if(t.c){send(t.c,{t:'me',me:me(t.c)});if(canCode(t.c))send(t.c,codesMsg(t.c))}lobby()},
 redeem(c,m){if(!c.acct)return flash(c,'Sign up for an account to redeem codes','bad');
  const now=Date.now();if(c.rlock>now)return flash(c,'Too many wrong tries. Wait a minute.','warn');if(now-(c.lastRedeem||0)<1000)return;c.lastRedeem=now;
  const k=String(m.code||'').trim().toLowerCase(),x=hasCode(k)?db.codes[k]:null;
  if(!x){c.rfail=(c.rfail||0)+1;if(c.rfail>=8){c.rlock=now+6e4;c.rfail=0}return flash(c,'Invalid Code','bad')}
  if(!c.u.owner&&x.by&&lc(x.by)==lc(c.u.name))return flash(c,"You can't redeem your own code",'bad');
  if(x.used.length>=x.max)return flash(c,'Code is expired','bad');
  if(x.used.some(n=>lc(n)==lc(c.u.name)))return flash(c,'You already redeemed this code','warn');
  x.used.push(c.u.name);(x.log=x.log||[]).push({n:c.u.name,at:now});c.rfail=0;addXp(c,x.xp);save();send(c,{t:'redeemed',xp:x.xp});pushCodes()},
 limcreate(c,m){if(!c.u?.owner||!c.acct)return;const name=String(m.name||'').trim().replace(/\s+/g,' ');
  if(!/^[A-Za-z0-9 ]{2,20}$/.test(name)||filter.check(name))return flash(c,'Color name: 2-20 letters/numbers/spaces (no bad words)','bad');
  const kind=m.kind==='solid'?'solid':'gradient',anim=LIMANIM.includes(m.anim)?m.anim:(m.kind==='animated'?'flow':m.kind==='shine'?'shine':'none'),speed=Math.min(4,Math.max(.4,+m.speed||1)),hx=/^#[0-9a-f]{6}$/i;
  const stops=(Array.isArray(m.stops)?m.stops:[]).map(String).filter(x=>hx.test(x)).slice(0,3).map(x=>x.toLowerCase());
  if(!stops.length||(kind!=='solid'&&stops.length<2))return flash(c,'Pick '+(kind==='solid'?'a color':'at least 2 colors'),'bad');
  if(kind==='solid'&&anim==='flow')return flash(c,'Flow needs a gradient (2 or more colors)','bad');
  const id='l_'+name.toLowerCase().replace(/[^a-z0-9]/g,'');if(hasLim(id))return flash(c,'A limited color with that name already exists','bad');
  if(Object.keys(db.limcolors).length>=40)return flash(c,'Too many limited colors (max 40). Delete one first.','bad');
  db.limcolors[id]={id,name,kind,anim,speed,price:Math.max(0,Math.min(1e7,Math.floor(+m.price)||0)),stops:kind==='solid'?stops.slice(0,1):stops};save();pushLim();send(c,{t:'limmade',id,name});flash(c,'Limited color "'+name+'" created','ok')},
 limprice(c,m){if(!c.u?.owner||!c.acct)return;const id=String(m.id||'');if(!hasLim(id)||id===THX_ID)return;const p=Math.max(0,Math.min(1e7,Math.floor(+m.price)||0));db.limcolors[id].price=p;save();pushLim();for(const x of online.values())send(x,shopMsg());flash(c,p?db.limcolors[id].name+' is now in the shop for '+p.toLocaleString('en-US')+' XP':db.limcolors[id].name+' removed from the shop','ok')},
 limdel(c,m){if(!c.u?.owner||!c.acct)return;const id=String(m.id||'');if(!hasLim(id))return;delete db.limcolors[id];
  for(const u of Object.values(db.users)){if(u.lim)u.lim=u.lim.filter(x=>x!==id);if(u.color===id)u.color='white'}
  for(const r of db.raffles)if(!r.done&&r.reward.color===id)r.reward.color='';
  for(const p of parties.values())if(p.reward&&p.reward.color===id)p.reward.color='';
  save();pushLim();for(const x of online.values())if(x.u)send(x,{t:'me',me:me(x)});lobby();pushRafflesNow()},
 megacreate(c,m){if(!c.u?.owner||!c.acct)return;if(c.party||c.bt||c.end)return flash(c,'Finish what you are doing first','warn');
  const rw=rwNorm(m.reward);if(!rw)return flash(c,'Choose a winner reward (XP, a limited color or a multiplier)','bad');
  const max=Math.max(2,Math.min(30,Math.floor(+m.max)||30));let name=String(m.name||'').trim().slice(0,30);if(name&&filter.check(name))name='';
  if(c.pend){clearTimeout(c.pend.tm);send(c.pend.to,{t:'chalgone',from:c.u.name});c.pend=null}
  if(c.watch){c.watch.spec.delete(c);c.watch=null}
  c.plob=true;lobby();send(c,{t:'plist',list:ptList()});
  const x={c,u:c.u,lives:PLIVES,out:true,left:false,spec:true},p={id:'p'+Date.now().toString(36)+Math.random().toString(36).slice(2,5),code:ptCode(),priv:!!m.priv,state:'lobby',m:[x],host:x,chain:[],turn:0,tok:0,deadline:0,msg:'',result:null,tm:null,max,mega:true,name,reward:rw,done:false};
  c.party=p;parties.set(p.id,p);ptPush(p);ptSendList();lobby();
  if(!p.priv)for(const y of online.values())send(y,{t:'announce',text:'🏟️ MEGA LOBBY open ('+max+' players)! Winner gets '+rwText(rw)+'. Open Multiplayer Mode!',from:dn(c.u)})},
 raffles(c){sendRaffles(c)},
 rafflenew(c,m){if(!c.u?.owner||!c.acct)return;const rw=rwNorm(m.reward);if(!rw)return flash(c,'Choose a prize (XP, a limited color or a multiplier)','bad');
  const title=String(m.title||'').trim().slice(0,30);if(title&&filter.check(title))return flash(c,'Please keep the title clean','bad');
  const winners=Math.floor(+m.winners),mins=Math.floor(+m.mins);
  if(!(winners>=1&&winners<=100))return flash(c,'Winners: 1 to 100','bad');if(!(mins>=1&&mins<=20160))return flash(c,'Duration: 1 minute to 14 days','bad');
  if(db.raffles.filter(r=>!r.done).length>=10)return flash(c,'Too many live raffles (max 10)','warn');
  const r={id:Date.now()*1000+Math.floor(Math.random()*1000),title,reward:rw,winners,endsAt:Date.now()+mins*60000,entries:[],done:false,win:[],at:Date.now()};
  db.raffles.push(r);const di=db.raffles.findIndex(x=>x.done);if(db.raffles.length>80&&di>=0)db.raffles.splice(di,1);
  schedR(r);save();pushRafflesNow();flash(c,'Raffle started!','ok');
  for(const x of online.values())send(x,{t:'announce',text:'🎟️ New raffle'+(title?': '+title:'')+'! Prize: '+rwText(rw)+'. Tap Raffle to enter!',from:dn(c.u)})},
 raffleenter(c,m){if(!c.acct)return flash(c,'Sign up for an account to enter raffles','bad');if(c.u.owner)return flash(c,'The owner cannot enter raffles','warn');
  const r=db.raffles.find(x=>x.id===m.id);if(!r||r.done||Date.now()>=r.endsAt)return flash(c,'This raffle has ended','warn');
  if(r.entries.includes(c.u.name))return flash(c,'You already entered!','warn');
  r.entries.push(c.u.name);save();flash(c,'🎟️ You are in the raffle! Good luck!','ok');qProg(c,'raffle');pushRaffles()},
 raffledel(c,m){if(!c.u?.owner||!c.acct)return;const i=db.raffles.findIndex(x=>x.id===m.id);if(i<0)return;const r=db.raffles[i];clearTimeout(rtim.get(r.id));rtim.delete(r.id);db.raffles.splice(i,1);save();pushRafflesNow()},
 plobby(c,m){if(m.on){if(c.bt||c.end)return flash(c,'Finish what you are doing first','warn');
   if(c.pend){clearTimeout(c.pend.tm);send(c.pend.to,{t:'chalgone',from:c.u.name});c.pend=null}
   if(c.watch){c.watch.spec.delete(c);c.watch=null}
   c.plob=true;lobby();send(c,{t:'plist',list:ptList()})}
  else{ptLeave(c);c.plob=false;lobby();ptSendList()}},
 pcreate(c,m){if(!c.plob||c.party||c.bt||c.end)return;if(parties.size>=200)return flash(c,'Too many parties right now, try again soon','warn');
  if(Date.now()-(c.lastParty||0)<1500)return;c.lastParty=Date.now();
  const x={c,u:c.u,lives:PLIVES,out:false,left:false},p={id:'p'+Date.now().toString(36)+Math.random().toString(36).slice(2,5),code:ptCode(),priv:!!m.priv,state:'lobby',m:[x],host:x,chain:[],turn:0,tok:0,deadline:0,msg:'',result:null,tm:null,max:PMAX};
  c.party=p;parties.set(p.id,p);ptPush(p);ptSendList();lobby()},
 pjoin(c,m){if(!c.plob||c.party||c.bt||c.end)return;let p;
  if(m.code!=null){const q=String(m.code).toUpperCase().replace(/[^A-Z0-9]/g,'');p=[...parties.values()].find(x=>x.priv&&x.code===q);if(!p)return flash(c,'No private party with that code','bad')}
  else{p=parties.get(String(m.id));if(!p||p.priv)return flash(c,'That party no longer exists','bad')}
  if(p.state!=='lobby')return flash(c,'That game already started','warn');if(p.done)return flash(c,'That Mega Lobby has ended','warn');if(p.mega&&!c.acct)return flash(c,'Sign up for an account to join Mega Lobbies','bad');
  if(ptCount(p)>=p.max)return flash(c,'That party is full (max '+p.max+' players)','warn');
  p.m.push({c,u:c.u,lives:PLIVES,out:false,left:false});c.party=p;ptPush(p);ptSendList();lobby()},
 pleave(c){ptLeave(c);send(c,{t:'pgone'});send(c,{t:'plist',list:ptList()});lobby()},
 pstart(c){const p=c.party;if(!p||p.state!=='lobby'||p.host.c!==c)return;if(p.done)return flash(c,'This Mega Lobby has ended','warn');if(ptCount(p)<2)return flash(c,'You need at least 2 players to start','warn');if(p.mega)for(const x of p.m)if(!x.spec&&x.c)qProg(x.c,'mega');ptStartGame(p)},
 psubmit(c,m){ptSubmit(c,m.word)},
 ptype(c,m){const p=c.party;if(!p||p.state!=='playing'||!p.m[p.turn]||p.m[p.turn].c!==c)return;const txt=filter.clean(String(m.text||'').slice(0,24));for(const x of p.m)if(!x.left&&x.c!==c)send(x.c,{t:'ptyping',text:txt})},
 color(c,m){const k=COLORS.find(x=>x[0]==m.color),own=c.u.owner;if((k&&(own||c.u.xp>=k[1]))||(own&&m.color=='ownerrainbow')||ownsLim(c.u,m.color)){c.u.color=m.color;if(c.acct)save();send(c,{t:'me',me:me(c)});lobby()}},
 shopget(c){send(c,shopMsg())},
 buylim(c,m){const u=c.u;if(!u)return;const id=String(m.id||''),d=hasLim(id)&&db.limcolors[id],isT=id===THX_ID,price=isT?THX_PRICE:(d&&d.price>0?d.price:0);if(!d||!price||(isT&&!thxOn()))return flash(c,'That item is no longer available','bad');if(ownsLim(u,id))return flash(c,'You already own it','bad');if(!canPay(u,price))return flash(c,'You need '+price.toLocaleString('en-US')+' XP to buy this','bad');spend(u,price);u.lim=u.lim||[];u.lim.push(id);if(c.acct)save();send(c,{t:'me',me:me(c)});send(c,shopMsg());flash(c,'You got '+d.name+'! Pick it from your color menu','ok')},
 buytheme(c,m){const u=c.u;if(!u||m.id!=='rainbow')return;if(u.owner||(u.themes||[]).includes('rainbow'))return flash(c,'You already own it','bad');if(!canPay(u,RB_PRICE))return flash(c,'You need '+RB_PRICE.toLocaleString('en-US')+' XP to buy this','bad');spend(u,RB_PRICE);u.themes=u.themes||[];u.themes.push('rainbow');if(c.acct)save();send(c,{t:'me',me:me(c)});flash(c,'Rainbow theme unlocked! Pick it in Themes 🌈','ok')},
 buy(c,m){const p=SHOP[m.mult];if(p&&canPay(c.u,p)&&c.u.mult<+m.mult&&!c.u.owner){spend(c.u,p);c.u.mult=+m.mult;if(c.acct)save();send(c,{t:'me',me:me(c)})}},
 announce(c,m){if(!canAnn(c))return;const t=String(m.text||'').trim().slice(0,140);if(!t||Date.now()-(c.lastAnn||0)<3000)return;c.lastAnn=Date.now();for(const x of online.values())send(x,{t:'announce',text:t,from:dn(c.u)})},
 warn(c,m){if(!isMod(c))return;const t=target(m.to);if(!t||!t.c||!canHit(c,t.u))return;const x=String(m.text||'').trim().slice(0,100)||'Please follow the rules.';t.u.warns=(t.u.warns||0)+1;if(t.c.acct)save();send(t.c,{t:'warned',text:x,count:t.u.warns,by:dn(c.u)})},
 clancreate(c,m){if(!c.acct)return flash(c,'Sign up for an account to make a clan','bad');const u=c.u;if(u.clan)return flash(c,'You are already in a clan','bad');if(u.creq)return flash(c,'Cancel your pending join request first','bad');
  const n=String(m.name||'').trim();if(!/^[A-Za-z0-9]{2,10}$/.test(n))return flash(c,'Clan name: 2 to 10 letters or numbers','bad');if(filter.check(n)||(RESERVED.test(n)&&!u.owner))return flash(c,'That clan name is not allowed','bad');
  if(db.clans[clanKey(n)])return flash(c,'That clan name is taken','bad');
  const cl={name:n,leader:u.name,members:[u.name],req:[],at:Date.now()};db.clans[clanKey(n)]=cl;u.clan=clanKey(n);save();flash(c,'Clan ['+n+'] created!','ok');clanSelf(c);clanPush(cl);lobby()},
 clanjoin(c,m){if(!c.acct)return flash(c,'Sign up for an account to join a clan','bad');const u=c.u,cl=db.clans[clanKey(String(m.name||''))];if(!cl)return flash(c,'Clan not found','bad');
  if(u.clan)return flash(c,'You are already in a clan','bad');if(u.creq)return flash(c,'You already have a pending request. Cancel it first.','bad');if(cl.members.length>=CLANMAX)return flash(c,'That clan is full','bad');if(cl.req.length>=30)return flash(c,'That clan has too many pending requests','bad');
  cl.req.push(u.name);u.creq=clanKey(cl.name);save();inboxAdd(cl.leader,true,{kind:'clan',text:'⚔️ '+dn(u)+' wants to join your clan ['+cl.name+']'});flash(c,'Request sent to ['+cl.name+']','ok');clanSelf(c);clanPush(cl);send(c,clanView(cl,c))},
 clancancel(c){if(!c.acct||!c.u.creq)return;const cl=db.clans[c.u.creq];if(cl)cl.req=cl.req.filter(n=>lc(n)!=lc(c.u.name));c.u.creq='';save();clanSelf(c);if(cl)clanPush(cl)},
 clanresp(c,m){if(!c.acct)return;const cl=clanOf(c.u);if(!cl||lc(cl.leader)!=lc(c.u.name))return;const i=cl.req.findIndex(n=>lc(n)==lc(m.from));if(i<0)return;const k=acctName(m.from),a=k&&db.users[k];
  if(m.accept&&a&&!a.clan&&cl.members.length>=CLANMAX)return flash(c,'Your clan is full (max '+CLANMAX+')','bad');
  cl.req.splice(i,1);if(a&&a.creq==clanKey(cl.name))a.creq='';
  if(a){if(m.accept){if(a.clan)flash(c,dn(a)+' is already in another clan','bad');else{cl.members.push(a.name);a.clan=clanKey(cl.name);inboxAdd(a.name,true,{kind:'clan',text:'🎉 You were accepted into ['+cl.name+']!'});flash(c,dn(a)+' joined your clan','ok')}}else inboxAdd(a.name,true,{kind:'clan',text:'❌ ['+cl.name+'] declined your join request'})}
  save();clanPush(cl);if(a)clanSelf(find(a.name));lobby()},
 clanleave(c){if(!c.acct||!c.u.clan)return;const name=clanTagOf(c.u),cl=clanDrop(c.u);save();flash(c,'You left ['+name+']','ok');clanSelf(c);if(cl)clanPush(cl);lobby()},
 clankick(c,m){if(!c.acct)return;const cl=clanOf(c.u);if(!cl||lc(cl.leader)!=lc(c.u.name))return;const k=acctName(m.name),t=k&&db.users[k];if(!t||t===c.u||t.clan!=clanKey(cl.name))return;
  clanDrop(t);inboxAdd(t.name,true,{kind:'clan',text:'🚪 You were removed from ['+cl.name+']'});save();clanSelf(find(t.name));clanPush(cl);lobby()},
 clandisband(c){if(!c.acct)return;const cl=clanOf(c.u);if(!cl||lc(cl.leader)!=lc(c.u.name))return;const ms=cl.members.slice();for(const n of ms)if(lc(n)!=lc(c.u.name))inboxAdd(n,true,{kind:'clan',text:'💥 The clan ['+cl.name+'] was disbanded'});clanDisband(cl);save();for(const n of ms)clanSelf(find(n));flash(c,'Clan disbanded','ok');lobby()},
 clanview(c,m){const cl=db.clans[clanKey(String(m.name||''))];send(c,cl?clanView(cl,c):{t:'clanview',gone:true,name:String(m.name||'')})},
 clanlist(c,m){const q=lc(String(m.q||'').trim()).slice(0,10);send(c,{t:'clanlist',list:Object.values(db.clans).filter(x=>!q||lc(x.name).includes(q)).map(x=>({name:x.name,n:x.members.length,total:Math.round(clanTotal(x)),full:x.members.length>=CLANMAX})).sort((a,b)=>b.total-a.total).slice(0,30)})},
 calget(c){send(c,{t:'cal',list:db.calendar})},
 calsave(c,m){if(!isMod(c))return;const t=String(m.title||'').trim().slice(0,50),d=String(m.details||'').trim().slice(0,600),date=String(m.date||''),time=String(m.time||'');
  if(!t)return flash(c,'Give the event a title','bad');if(!/^\d{4}-\d{2}-\d{2}$/.test(date)||isNaN(new Date(date+'T12:00:00Z'))||date<'2000-01-01'||date>'2100-01-01')return flash(c,'Pick a valid date','bad');
  if(time&&!/^([01]\d|2[0-3]):[0-5]\d$/.test(time))return flash(c,'Invalid time','bad');if(filter.check(t)||filter.check(d))return flash(c,'Event text contains a word that is not allowed','bad');
  const cur=m.id?db.calendar.find(e=>e.id===m.id):null;if(m.id&&!cur)return flash(c,'Event not found','bad');
  if(cur){Object.assign(cur,{title:t,details:d,date,time,edited:dn(c.u)})}else{if(db.calendar.length>=500)return flash(c,'Calendar is full (500 events). Delete old ones.','bad');db.calendar.push({id:Date.now()*1000+Math.floor(Math.random()*1000),title:t,details:d,date,time,by:dn(c.u),at:Date.now()})}
  db.calendar.sort((a,b)=>a.date.localeCompare(b.date)||a.time.localeCompare(b.time)||a.at-b.at);save();flash(c,cur?'Event updated':'Event added','ok');pushCal()},
 caldel(c,m){if(!isMod(c))return;const i=db.calendar.findIndex(e=>e.id===m.id);if(i<0)return;db.calendar.splice(i,1);save();flash(c,'Event deleted','ok');pushCal()},
 pstats(c,m){if(!c.u||Date.now()-(c.psAt||0)<100)return;c.psAt=Date.now();const k=String(m.name||'').slice(0,24),x=find(k),u=x?x.u:db.users[acctName(k)];if(!u)return;
  const acct=x?!!x.acct:true,o=!!u.owner,g=acct&&!o?roll(u):null;
  send(c,{t:'pstats',name:u.name,dn:dn(u),owner:o,acct,xp:o?null:u.xp||0,mult:u.mult||1,today:g?g.dx:0,week:g?g.wx:0,month:g?g.mx:0,rank:acct&&!o?rankOf(u).all.rank:0,secs:acct?Math.round(u.secs||0):0,since:acct?u.born||0:0,clan:clanTagOf(u),friends:acct?(u.friends||[]).length:0,status:x?(x.inact?'away':x.end?'endless':x.plob?'multiplayer':x.bt?'in battle':x.watch?'watching a battle':'online'):'offline'})},
 quests(c){if(c.u)send(c,qView(c))},
 questsave(c,m){if(!canQ(c))return;const type=String(m.type||'');if(!QT[type])return flash(c,'Pick a quest type','bad');
  const target=Math.min(type==='xp'?100000:100,Math.max(1,Math.floor(+m.target)||1)),title=String(m.title||'').trim().slice(0,60);if(title&&filter.check(title))return flash(c,'That title is not allowed','bad');
  const r=rwNorm(m.reward);if(!r)return flash(c,'Pick a reward (XP, a limited color or a multiplier)','bad');
  if(!c.u.owner){if(r.mult)return flash(c,'Only the owner can give XP multipliers','bad');if(r.xp>5000)return flash(c,'Quest mods can give up to 5,000 XP per quest','bad')}
  const cur=m.id!=null?db.quests.find(q=>q.id===m.id):null;if(m.id!=null&&!cur)return flash(c,'Quest not found','bad');const on=m.on!==false;
  if(cur)Object.assign(cur,{type,target,title,reward:r,on,edited:dn(c.u)});else{if(db.quests.length>=15)return flash(c,'Max 15 quests. Delete one first.','bad');db.quests.push({id:++db.questSeq,type,target,title,reward:r,on,by:dn(c.u),byu:c.u.name,at:Date.now()})}
  save();flash(c,cur?'Quest updated':'Quest added','ok');pushQuests()},
 questdel(c,m){if(!canQ(c))return;const i=db.quests.findIndex(q=>q.id===m.id);if(i<0)return;db.quests.splice(i,1);save();flash(c,'Quest deleted','ok');pushQuests()},
 questclaim(c,m){if(!c.acct||c.u.owner)return;const q=db.quests.find(x=>x.id===m.id&&x.on);if(!q)return;if(qMine(c.u,q))return flash(c,"You can't claim a quest you made",'bad');const d=qDay(c.u);if(d.c.includes(q.id))return flash(c,'Already claimed today','warn');if(qDone(c.u,q)<q.target)return flash(c,'Quest not finished yet','warn');
  d.c.push(q.id);qLogDone(c.u,q);db.qlog[ymd()][q.id][c.u.name].claimed=Date.now();giveReward(c.u.name,q.reward);save();flash(c,'🎁 Quest reward: '+rwText(q.reward),'ok');qSend(c)},
 setqmod(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t||t.u.owner||db.users[t.u.name]!==t.u)return;t.u.qmod=!!m.on;save();flash(c,dn(t.u)+(t.u.qmod?' can now moderate Daily Quests':' is no longer a quest moderator'),'ok');const x=find(t.u.name);if(x&&x.u===t.u){send(x,{t:'me',me:me(x)});if(t.u.qmod)flash(x,'You can now moderate Daily Quests!','ok');qSend(x)}},
 logs(c){if(c.u)send(c,{t:'logs',list:c.u.log||[],acct:!!c.acct})},
 questwho(c,m){if(!canQ(c))return;const q=db.quests.find(x=>x.id===m.id);if(!q)return;const ql=db.qlog||{},today=ymd(),day=ql[m.day]?String(m.day):today,ent=((ql[day]||{})[q.id])||{};
  const days=Object.keys(ql).filter(d=>ql[d][q.id]&&Object.keys(ql[d][q.id]).length).sort().reverse();if(!days.includes(today))days.unshift(today);
  let inprog=0;if(day===today)for(const u of Object.values(db.users)){if(u.owner||ent[u.name])continue;const pr=q.type==='xp'?roll(u).dx:(u.qd&&u.qd.d===today?(u.qd.p[q.id]||0):0);if(pr>0)inprog++}
  send(c,{t:'questwho',id:q.id,title:qTitle(q),target:q.target,day,today,days,inprog,list:Object.entries(ent).map(([n,v])=>({...pubN(n),at:v.at,claimed:v.claimed||0})).sort((a,b)=>a.at-b.at)})},
  acctlist(c,m){if(!c.u?.owner||!c.acct)return;const q=lc(String(m.q||'').trim()).slice(0,20),all=Object.values(db.users).filter(u=>!q||lc(u.name).includes(q)||lc(u.display||'').includes(q));
  all.sort((a,b)=>(find(b.name)?1:0)-(find(a.name)?1:0)||(b.seen||0)-(a.seen||0)||lc(a.name).localeCompare(lc(b.name)));send(c,{t:'acctlist',q,total:all.length,list:all.slice(0,40).map(acctRow)})},
 acctview(c,m){if(!c.u?.owner||!c.acct)return;const k=acctName(m.name),u=k&&db.users[k];if(!u)return send(c,{t:'acctview',gone:true,name:String(m.name||'')});send(c,{t:'acctview',...acctDetail(u)})},
 banlinked(c,m){if(!c.u?.owner||!c.acct)return;const k=acctName(m.to),u=k&&db.users[k];if(!u||u.owner)return flash(c,'Account not found','bad');
  const mins=Math.min(525600,Math.max(0,Math.floor(+m.mins)||0)),reason=String(m.reason||'Linked accounts').slice(0,80),term=!!m.terminate,lk=linkedOf(u),until=mins?Date.now()+mins*6e4:0;
  for(const d of lk.devs)db.devbans[d]={at:Date.now(),until,reason,by:dn(c.u),from:u.name,term};
  const names=lk.users.map(x=>x.name);for(const x of lk.users){if(term)terminateAcct(x,reason,dn(c.u));else banAcct(x,reason,dn(c.u),mins)}
  for(const o of online.values())if(o.dev&&lk.devs.includes(o.dev)&&!(o.u&&o.u.owner)){send(o,banMsg({until,reason}));setTimeout(()=>o.ws.close(),300)}
  save();console.log('BANLINKED',names.join(','),'devices',lk.devs.length,'terminate',term);flash(c,(term?'Terminated ':'Banned ')+names.length+' account(s) and blocked '+lk.devs.length+' device(s)','ok');send(c,{t:'acctdone',name:u.name})},
 unbanlinked(c,m){if(!c.u?.owner||!c.acct)return;const k=acctName(m.to),u=k&&db.users[k];if(!u)return flash(c,'Account not found (terminated accounts are deleted)','bad');
  const lk=linkedOf(u);for(const d of new Set([...lk.devs,...(u.devs||[])]))delete db.devbans[d];for(const x of lk.users)delete db.bans[lc(x.name)];save();flash(c,'Unbanned '+lk.users.length+' account(s) and cleared their devices','ok');send(c,{t:'acctdone',name:u.name})},
 acctterminate(c,m){if(!c.u?.owner||!c.acct)return;const k=acctName(m.to),u=k&&db.users[k];if(!u||u.owner)return flash(c,'Account not found','bad');
  const dv=(u.devs||[]).filter(d=>!ownerDev(d));if(m.devices)for(const d of dv)db.devbans[d]={at:Date.now(),until:0,reason:'Account terminated',by:dn(c.u),from:u.name,term:true};
  terminateAcct(u,String(m.reason||'Account terminated'),dn(c.u));save();flash(c,u.name+' terminated','ok');send(c,{t:'acctdone',name:u.name,gone:true})},
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
 liveev(c){if(c.acct)send(c,liveStatus(c))},
 setliveev(c,m){if(!c.u?.owner||!c.acct)return;const u=fuser(m.to);if(!u||u.owner)return flash(c,'Only regular accounts can get live events','bad');
  if(m.on)u.lev={limit:Math.max(1,Math.min(50,Math.floor(+m.limit)||3))};else delete u.lev;save();
  const o=find(u.name);if(o&&o.acct){send(o,{t:'me',me:me(o)});send(o,liveStatus(o))}lobby();flash(c,m.on?'Live events granted ('+u.lev.limit+' per day)':'Live events revoked','ok')},
 spawnevent(c,m){if(!c.u||!c.acct)return;const kind=m.kind==='blackhole'?'blackhole':m.kind==='stampede'?'stampede':m.kind==='turkey'?'turkey':'token';
  if(c.u.owner){if(evt)return flash(c,'An event is already running','warn');return startEvent(c.u,kind)}
  if(!c.u.lev)return;if(evLeft(c.u)<=0)return flash(c,'You used all '+c.u.lev.limit+' of your events today','warn');if(evt)return flash(c,'An event is already running. Try again in a moment.','warn');
  if(kind==='turkey'){const k=lc(c.u.name),now=Date.now(),p=evPend.get(k);if(p&&now-p.at<30000)return flash(c,'Request already sent. Wait for the owner to answer.','warn');
   const ow=[...online.values()].find(x=>x.u&&x.u.owner&&x.acct);if(!ow)return flash(c,'The owner must be online to approve a Turkey Event','warn');
   const id=now+'-'+Math.random().toString(36).slice(2,7);evPend.set(k,{id,at:now,u:c.u});setTimeout(()=>{const q=evPend.get(k);if(q&&q.id===id){evPend.delete(k);const o=find(ow.u.name);if(o)send(o,{t:'evreqgone',id})}},60000);
   send(ow,{t:'evreq',id,from:c.u.name,dn:dn(c.u),kind:'turkey'});return flash(c,'Request sent. Waiting for the owner to accept…','ok')}
  startEvent(c.u,kind);const d=ymd(),n=c.u.evUsed&&c.u.evUsed.d===d?c.u.evUsed.n:0;c.u.evUsed={d,n:n+1};save();send(c,liveStatus(c))},
 evresp(c,m){if(!c.u?.owner||!c.acct)return;let k=null,p=null;for(const[a,b]of evPend)if(b.id===m.id){k=a;p=b}if(!p)return send(c,{t:'evreqgone',id:m.id});evPend.delete(k);send(c,{t:'evreqgone',id:m.id});
  const r=[...online.values()].find(x=>x.u===p.u);if(!r)return;if(!m.ok)return flash(r,'The owner denied your Turkey Event','bad');
  if(!p.u.lev||evLeft(p.u)<=0)return flash(r,'You have no events left today','warn');if(evt)return flash(r,'Approved, but another event is running. Ask again in a moment.','warn');
  startEvent(p.u,'turkey');const d=ymd(),n=p.u.evUsed&&p.u.evUsed.d===d?p.u.evUsed.n:0;p.u.evUsed={d,n:n+1};save();send(r,liveStatus(r));flash(r,'The owner approved your Turkey Event! 🦃','ok')},
 buyevent(c){if(!c.u)return;if(c.u.owner)return flash(c,'You can spawn it free from the 🛠️ Tools button','ok');
  if(evt||Date.now()<evtCool)return flash(c,'A token explosion just ran or is running. Try again in a bit.','warn');
  if(c.u.bal<EV_COST||c.u.xp<EV_COST)return flash(c,'You need 10,000 XP to buy a Token Explosion','bad');
  c.u.xp-=EV_COST;c.u.bal-=EV_COST;gain(c.u,-EV_COST);{const k=COLORS.find(x=>x[0]==c.u.color);if(k&&c.u.xp<k[1])c.u.color='white'}if(c.acct)save();send(c,{t:'me',me:me(c)});startEvent(c.u)},
 coin(c,m){const e=evt;if(!e||m.ev!==e.id)return;const cn=e.coins.get(m.id|0);if(!cn)return;const now=Date.now()-e.coinsAt;if(now<cn.t-1500||now>cn.t+cn.life+2500)return;
  const k=lc(c.u.name)+(c.acct?'':'#g'),set=e.claims[k]=e.claims[k]||new Set();if(set.has(cn.id)||Date.now()-(c.lastCoin||0)<60)return;c.lastCoin=Date.now();set.add(cn.id);
  const xp=cn.mega?500:cn.inv?300:cn.big?100:10;addXp(c,xp);qProg(c,'event');send(c,{t:'coinok',id:cn.id,xp,big:cn.big||!!cn.inv,mega:!!cn.mega})},
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
 endstart(c){if(c.bt||c.watch||c.end||c.plob)return;if(c.pend){clearTimeout(c.pend.tm);c.pend=null}c.end={chain:[startWord()],xp:0,words:0,streak:0,best:0,turn:'you',busy:false};esend(c,'Go! Say a word that connects.');lobby()},
 async endsubmit(c,m){const e=c.end;if(!e||e.turn!=='you'||e.busy)return;const w=String(m.word||'').toLowerCase().trim();
  if(!/^[a-z]{2,20}$/.test(w))return flash(c,'One word, letters only','bad');
  if(filter.check(w)){flash(c,'That word does not count.','bad');return strike(c)}
  if(e.xp>=ENDCAP)return flash(c,'You hit the XP cap for this run. Press Stop to collect!','warn');
  e.busy=true;const ok=!e.chain.includes(w)&&await rel(e.chain.at(-1),w);e.busy=false;if(c.end!==e)return;
  if(!ok){flash(c,'That is unrelated!','bad');eh(e,{k:'x',w,by:'you'});e.chain=[startWord()];e.hist.push({k:'r',w:e.chain[0]});e.streak=0;return esend(c,'Oops, that did not connect. New word!')}
  eh(e,{k:'w',w,by:'you'});e.chain.push(w);e.words++;e.streak++;e.best=Math.max(e.best,e.streak);addEnd(e,ENDWORD);e.turn='bot';esend(c,'✅ Nice one!');setTimeout(()=>botMove(c),1000+Math.random()*1500)},
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
 endpoll(c){if(canAnn(c)){if(poll&&!poll.done)poll.endedBy=dn(c.u);endPoll()}},
 vote(c,m){if(!poll||poll.done||Date.now()>poll.endsAt||m.id!==poll.id)return;const i=m.i|0;if(i<0||i>=poll.opts.length)return;poll.votes[pkey(c)]=i;clearTimeout(pollBc);pollBc=setTimeout(bcPoll,250)},
 active(c){c.lastAct=Date.now();if(c.inact){c.inact=false;lobby()}},
 vis(c,m){c.hiddenSince=m.hidden?Date.now():0},
 lb(c){if(Date.now()-(c.lbAt||0)<3000)return;c.lbAt=Date.now();send(c,{t:'lb',...lbData(),fr:c.acct&&c.u?friendLb(c.u):null,clans:clanBoards()})},
 lbfind(c,m){if(Date.now()-(c.lbfAt||0)<400)return;c.lbfAt=Date.now();const q=String(m.q||'').trim().slice(0,16).toLowerCase();if(!q)return send(c,{t:'lbfind',q:'',exact:null,matches:[]});
  const us=Object.values(db.users),ex=us.find(x=>x.name.toLowerCase()==q||String(x.display||'').toLowerCase()==q),ms=us.filter(x=>x!==ex&&(x.name.toLowerCase().includes(q)||String(x.display||'').toLowerCase().includes(q))).slice(0,8).map(pub);
  send(c,{t:'lbfind',q,exact:ex?{...pub(ex),ranks:rankOf(ex)}:null,matches:ms})},
 syncbal(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t||t.u.owner)return;t.u.bal=Math.max(0,t.u.xp);save();if(t.c)send(t.c,{t:'me',me:me(t.c)});flash(c,t.u.name+"'s balance set to "+t.u.xp.toLocaleString('en-US')+' XP','ok')},
 grant(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t)return;const n=Math.max(-1e6,Math.min(1e6,+m.xp|0));t.u.xp=Math.max(0,t.u.xp+n);gain(t.u,n);{const k=COLORS.find(x=>x[0]==t.u.color);if(k&&!t.u.owner&&t.u.xp<k[1])t.u.color='white'}t.u.bal=Math.max(0,t.u.bal+n);save();if(t.c)send(t.c,{t:'me',me:me(t.c)});lobby()},
 settag(c,m){if(!c.u?.owner||!c.acct)return;const t=target(m.to);if(!t||t.u.owner)return;const h=/^#[0-9a-f]{6}$/i,k=t.u.name.toLowerCase(),x=String(m.text||'').slice(0,16);
  if(!x)delete db.tags[k];else db.tags[k]={text:x,c1:h.test(m.c1)?m.c1:'#dddddd',c2:h.test(m.c2)?m.c2:'#aaaaaa'};t.u.tag='';save();lobby()},
 ownertag(c,m){if(!c.u?.owner||!c.acct)return;const h=/^#[0-9a-f]{6}$/i;if(h.test(m.c1)&&h.test(m.c2)){db.ownerTag={c1:m.c1,c2:m.c2};save();lobby()}}};
const types={'.html':'text/html','.js':'text/javascript','.css':'text/css','.png':'image/png','.gif':'image/gif','.jpg':'image/jpeg','.webp':'image/webp','.svg':'image/svg+xml','.ico':'image/x-icon','.mp3':'audio/mpeg'};
const ASSETS=['projectile.png','projectexplosion.gif','black-hole-loop-animation-on-black-background-isolated-transparent-alpha-png.webp','pixil-frame-0.png','coinconnect.png'];
const srv=http.createServer((q,r)=>{let u='/';try{u=decodeURIComponent(q.url.split('?')[0])}catch{}
 const rel=u=='/'?'index.html':path.normalize(u).replace(/^(\.\.[\/\\])+/,'');
 const nf=()=>{r.writeHead(404);r.end('Not found')};
 const tryRead=(f,next)=>fs.readFile(f,(e,d)=>{if(e)return next();r.writeHead(200,{'Content-Type':types[path.extname(f)]||'text/plain'});r.end(d)});
 tryRead(path.join(__dirname,'public',rel),()=>{const b=path.basename(rel);if(ASSETS.includes(b))tryRead(path.join(__dirname,b),nf);else nf()})});
new WebSocketServer({server:srv}).on('connection',(ws,req)=>{const ip=req.headers['x-forwarded-for']?.split(',')[0]||req.socket.remoteAddress;
 const c={ws,ip,u:null};if(bans[ip]>Date.now()){send(c,{t:'banned'});return ws.close()}
 ws.on('message',d=>{let m;try{m=JSON.parse(d)}catch{return}if(m.t!=='guest'&&m.t!=='signup'&&m.t!=='login'&&m.t!=='resume'&&!c.u)return;if(typeof m.dev==='string'&&DEVRE.test(m.dev))c.dev=m.dev;if((m.t==='guest'||m.t==='signup'||m.t==='login'||m.t==='resume')&&devGate(c,m.name||db.tokens[m.tk]))return;handlers[m.t]?.(c,m)});
 ws.on('close',()=>{if(c.u)logout(c)})});
(async()=>{if(RURL){try{const r=await rcmd(['GET','connectchain']);if(r.result)db=JSON.parse(r.result);console.log('Loaded saved data from Upstash')}catch(e){console.log('Upstash load failed, exiting so saved data is not overwritten:',e.message);process.exit(1)}}
 db.users=db.users||{};db.tokens=db.tokens||{};db.tags=db.tags||{};db.bans=db.bans||{};db.devbans=db.devbans||{};db.clans=db.clans||{};db.calendar=db.calendar||[];db.quests=db.quests||[];db.questSeq=db.questSeq||0;db.modreqs=db.modreqs||[];db.ideas=db.ideas||[];db.rooms=db.rooms||{};db.reports=db.reports||[];db.codes=db.codes||{};db.limcolors=db.limcolors||{};db.raffles=db.raffles||[];db.ownerTag=db.ownerTag||{c1:'#ff0080',c2:'#00d4ff'};
 limSeed();db.raffles.forEach(r=>{if(!r.done)schedR(r)});ensureOwner();srv.listen(PORT,()=>console.log('ConnectChain on '+PORT))})();
