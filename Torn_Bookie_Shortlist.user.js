// ==UserScript==
// @name         Torn_Bookie_Shortlist
// @namespace    https://github.com/ShavedW00kie/
// @version      1.0.1
// @description  Evidence-only 24-hour Bookie shortlist, coverage reporting and optional external odds.
// @author       ShavedW00kie (Torn: ThaWookie [2954173] )
// @license      BSD-3-Clause
// @match        https://www.torn.com/page.php*
// @run-at       document-start
// @noframes
// @grant        GM_info
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_setClipboard
// @grant        GM_xmlhttpRequest
// @grant        GM.getValue
// @grant        GM.setValue
// @grant        GM.setClipboard
// @grant        GM.xmlHttpRequest
// @grant        unsafeWindow
// @connect      api.the-odds-api.com
// ==/UserScript==

(function (nativeInfo) {
'use strict';
if (location.hostname !== 'www.torn.com' || location.pathname !== '/page.php' || new URLSearchParams(location.search).get('sid') !== 'bookie') return;
const GM_info = nativeInfo || {script: {name: 'Torn_Bookie_Shortlist'}};
const MyDebug = initializeModularDebugger(GM_info.script.name);
/*
INSTALL: Tampermonkey > Create a new script > paste this whole file > Save.
TornPDA: add this file as a custom userscript; document-start capture is preferred.
Open https://www.torn.com/page.php?sid=bookie. Drag the header or collapsed ticket.
Settings defaults: x1.30 through x2.50 favorite; opponent x4.00 or higher; 24 hours.

COVERAGE LIMITATION: This release DOES NOT scan every Torn event automatically.
It observes loaded markets and never labels that subset as complete. Open sport
categories and expand matches to populate it. Only exhaustive two-competitor
2-Way Full event / 3-Way Ordinary time markets are supported. Race/outright
fields and unknown market scopes are excluded. Unknown event country/gender
remain unknown, and are excluded by specific filters. Country means event
country metadata, not participant nationality. Unlabeled men's events can be
excluded by the men's-only filter.

RANKING: p = (1/favorite_decimal) / sum(1/outcome_decimal), including the draw.
This is an odds-derived estimate, not a true or empirically verified win rate.
Top five are distinct events; fewer are shown when fewer qualify. Draw cannot
satisfy the opponent threshold. All comparisons use Torn multipliers.

EXTERNAL: Save a The Odds API key, load external sports, then refresh external.
One h2h market and one bookmaker region are requested per active competition.
A broad scan can consume many quota credits. The sports catalog is cached for
24h, odds for 5 minutes. Stop halts after the current request. Requests are
manual and sequential; failures stop the scan and preserve a partial status.
Only exact accent-normalized participants, start within 5 minutes, and matching
outcome sets are displayed. Ambiguous fixtures and stale quotes are excluded.
League and settlement compatibility are not proven, so external quotes do not
alter ranking. No web-derived performance statistics are fabricated.

PRIVACY: No Torn API key is needed or requested. Optional external keys go only
to The Odds API and are stored only with the remember checkbox in GM storage.
No key is put in localStorage. Preferences use localStorage as a fallback.
No bet placement, hidden-page crawling, or private betting-history export.

VALIDATION: Pure filtering and ranking checks plus a local DOM fixture are
used during development; live Torn/TornPDA integration requires user testing.
*/
const PREFIX = 'tw-shortlist-v1:';
const TTL = 5 * 60000, DAY = 86400000;
const defaults = {min:1.3,max:2.5,dog:4,sex:'both',region:'all',country:'US',sports:[],events:[],collapsed:false,x:12,y:90,providerRegion:'eu'};
let cfg = {...defaults}, key = '', root, resultBox, statusBox, settings, sportBox, eventBox, support;
let busy=false, stopped=false, frame=0, lastDOM='', providerStatus='External odds not loaded.', catalog=[];
const events=new Map(), external=new Map(), metadata=new Map(), cache=new Map();
const norm=s=>String(s??'').normalize('NFD').replace(/[\u0300-\u036f]/g,'').toLowerCase().replace(/[^a-z0-9]+/g,' ').trim();
const txt=n=>(n?.textContent||'').replace(/\s+/g,' ').trim();
const stamp=v=>{const n=Number(v);return Number.isFinite(n)&&n>1e9?(n<1e11?n*1000:n):typeof v==='string'&&/(Z|[+-]\d\d:\d\d)$/.test(v)?Date.parse(v):NaN;};
const log=(event,extra={},level='INFO')=>MyDebug.log({event,...extra},level);
async function get(k,d,secret=false){try{if(typeof GM_getValue==='function')return await GM_getValue(PREFIX+k,d);if(typeof GM!=='undefined'&&GM.getValue)return await GM.getValue(PREFIX+k,d);if(!secret)return JSON.parse(localStorage.getItem(PREFIX+k)||'null')??d;}catch(_){log('Storage read failed',{item:k},'WARN');}return d;}
async function put(k,v,secret=false){try{if(typeof GM_setValue==='function'){await GM_setValue(PREFIX+k,v);return true;}if(typeof GM!=='undefined'&&GM.setValue){await GM.setValue(PREFIX+k,v);return true;}if(!secret){localStorage.setItem(PREFIX+k,JSON.stringify(v));return true;}}catch(_){log('Storage write failed',{item:k},'WARN');}return false;}
function el(tag,text,cls){const n=document.createElement(tag);if(text!==undefined)n.textContent=text;if(cls)n.className=cls;return n;}
function button(label,fn){const b=el('button',label);b.type='button';b.addEventListener('click',fn);return b;}
function note(s){if(statusBox)statusBox.textContent=s;}
function route(hash){const m=String(hash).match(/^#\/([a-z0-9-]+)\/(\d+)\/?$/i);return m?{sport:m[1],id:m[2]}:null;}
function validMarket(e){
 if(!e||!/^\d+$/.test(e.id)||!e.sport||!Number.isFinite(e.start)||e.participants.length!==2)return false;
 if(!['2-Way Full event','3-Way Ordinary time'].includes(e.market))return false;
 const names=e.outcomes.map(o=>norm(o.name));
 if(names.length!==(e.market.startsWith('3')?3:2)||new Set(names).size!==names.length)return false;
 if(e.participants.some(p=>!names.includes(norm(p)))||new Set(e.participants.map(norm)).size!==2)return false;
 if(names.length===3&&!names.includes('draw'))return false;
 return e.outcomes.every(o=>o.name&&Number.isFinite(o.odds)&&o.odds>1&&o.odds<=1e6&&!o.suspended);
}
function gender(e){const s=norm(e.competition+' '+e.name);if(/\b(women|womens|female|ladies|wnba|wta)\b/.test(s))return 'women';if(/\b(men|mens|male|atp)\b/.test(s))return 'men';return 'unknown';}
function qualifying(e,now=Date.now()){
 if(!validMarket(e)||e.start<=now||e.start>now+DAY||now-e.at>TTL||e.at>now+30000)return null;
 if(cfg.sports.length&&!cfg.sports.includes(e.sport))return null;
 if(cfg.events.length&&!cfg.events.includes(e.id))return null;
 if(cfg.sex!=='both'&&gender(e)!==cfg.sex)return null;
 if(cfg.region!=='all'&&(!e.country||(cfg.region==='international'?e.country==='US':e.country!==(cfg.region==='us'?'US':cfg.country))))return null;
 const teams=e.outcomes.filter(o=>e.participants.some(p=>norm(p)===norm(o.name))).sort((a,b)=>a.odds-b.odds);
 if(teams.length!==2||teams[0].odds===teams[1].odds||teams[0].odds<cfg.min||teams[0].odds>cfg.max||teams[1].odds<cfg.dog)return null;
 // The candidate must also be the favorite against a possible draw.
 if(e.outcomes.some(o=>o.odds<teams[0].odds))return null;
 const total=e.outcomes.reduce((s,o)=>s+1/o.odds,0);
 return {e,favorite:teams[0],underdog:teams[1],p:(1/teams[0].odds)/total};
}
function rankings(now=Date.now()){
 const best=new Map();for(const e of events.values()){const q=qualifying(e,now);if(q&&(!best.has(e.id)||best.get(e.id).p<q.p))best.set(e.id,q);}
 return [...best.values()].sort((a,b)=>b.p-a.p||a.e.start-b.e.start||a.e.id.localeCompare(b.e.id)).slice(0,5);
}
function remember(e){const k=e.id+'|'+e.market;if(validMarket(e)){events.set(k,e);log('Market captured',{id:e.id,sport:e.sport,outcomes:e.outcomes.length});}else events.delete(k);}
function dateFromDOM(card){
 for(const n of card.querySelectorAll('[data-start-timestamp],[data-start-time],[data-start],time[datetime],[title]')){
  for(const a of ['data-start-timestamp','data-start-time','data-start','datetime','title']){const s=n.getAttribute(a);if(!s)continue;const t=stamp(s);if(Number.isFinite(t))return t;
   // Torn's countdown tooltip uses Torn City Time (UTC), not the browser timezone.
   const m=s.match(/^(?:Due to start at|Starts at)\s*(\d{1,2}):(\d{2})(?::(\d{2}))?\s*(?:-|on)\s*(\d{1,2})\/(\d{1,2})\/(\d{4})(?:\s*(?:TCT|UTC|GMT))?$/i);
   if(m){const t=Date.UTC(+m[6],+m[5]-1,+m[4],+m[1],+m[2],+(m[3]||0));const d=new Date(t);if(d.getUTCMonth()===+m[5]-1&&d.getUTCDate()===+m[4]&&d.getUTCHours()===+m[1])return t;}
  }
 }return NaN;
}
function clean(n){if(!n)return '';const c=n.cloneNode(true);c.querySelectorAll('.label,.tbma-inline').forEach(x=>x.remove());return txt(c);}
function scanDOM(){
 const cards=[...document.querySelectorAll('li.c-pointer')].filter(c=>c.querySelector('.matchName .name p'));
 const signature=location.hash+'|'+cards.map(c=>c.textContent+Array.from(c.querySelectorAll('[title]'),n=>n.title).join('|')).join('|');
 if(signature===lastDOM)return;lastDOM=signature;
 for(const card of cards){
  const r=(card.classList.contains('active')?route(location.hash):null)||[...card.querySelectorAll('a[href]')].map(a=>route(new URL(a.href,location.href).hash)).find(Boolean);
  if(!r)continue;
  const p=card.querySelector('.matchName .name p'),participants=[...p.querySelectorAll('b')].map(txt);
  const meta=metadata.get(r.id)||{},start=dateFromDOM(card),competition=txt(p).replace(/^.*?\s-\s/,'');
  const e={...r,name:participants.join(' v '),participants,competition,start:Number.isFinite(start)?start:meta.start,country:meta.country||'',at:Date.now()};
  if(participants.length!==2)continue;
  let readAny=false;
  for(const ul of card.querySelectorAll('ul.bets-wrap')){
   let m=null;const markets=[];
   for(const li of ul.children){if(!li.classList.contains('bets'))continue;const h=li.querySelector('.market-name-cell');
    if(h){m={market:txt(h.querySelector('.bold')),outcomes:[]};markets.push(m);continue;}
    if(!m)continue;const c=li.querySelector('.cells-wrap'),dest=c?.querySelector('.result'),o=c?.querySelector('.odds.decimal'),input=c?.querySelector('input.amount');
    if(!dest||!o)continue;m.outcomes.push({name:txt(dest.querySelector('span'))||txt(dest),odds:Number(clean(o).replace(/^x\s*/i,'')),suspended:!!input?.disabled||/suspended/i.test(input?.value||'')});
   }
   for(const m of markets){if(['2-Way Full event','3-Way Ordinary time'].includes(m.market)){remember({...e,...m});readAny=true;}}
  }
  // A newly disabled card invalidates earlier captured prices.
  if(card.classList.contains('disabled'))for(const [k,v]of events)if(v.id===r.id)events.delete(k);
  if(!readAny)log('Match needs expanded winner market',{id:r.id},'DEBUG');
 }
}
function consume(data){
 if(!data||typeof data!=='object')return;
 const payload=[data,data.data,data.response].find(x=>x&&(Array.isArray(x.gameBoxesList)||Array.isArray(x.outcomeTypes)))||data;
 for(const box of payload.gameBoxesList||[])for(const m of box.matches||[]){if(m?.ID)metadata.set(String(m.ID),{start:stamp(m.startTimestamp),country:/^[A-Za-z]{2}$/.test(m.countryCode||'')?m.countryCode.toUpperCase():''});}
 const m=payload.match;
 if(m?.ID){const id=String(m.ID);metadata.set(id,{start:stamp(m.startTimestamp),country:/^[A-Za-z]{2}$/.test(m.countryCode||'')?m.countryCode.toUpperCase():''});
  // Only explicit full market labels are accepted. Unknown scope IDs are not guessed.
  const sport=String(m.alias||'');
  for(const market of payload.outcomeTypes||[]){const name=String(market.name||market.outcome||'');if(!['2-Way Full event','3-Way Ordinary time'].includes(name))continue;
   const e={id,sport,name:String(m.name||''),competition:String(m.competition||''),participants:(m.ep||[]).map(p=>String(p.name||'')),...metadata.get(id),market:name,at:Date.now(),outcomes:(market.odds||[]).map(o=>({name:String(o.bettingoffer||o.label||''),odds:Number(o.odds),suspended:o.betIsAllowed!==true||o.active===false||Number(o.is_live)===1||/suspend|closed/i.test(String(o.state||''))}))};
   if(/^[a-z]+(?:-[a-z0-9]+)*$/.test(sport))remember(e);
  }
 }
 lastDOM='';schedule();
}
function isBookieURL(value){try{const u=new URL(String(value),location.href);return u.origin===location.origin&&u.pathname==='/page.php'&&u.searchParams.get('sid')==='bookieApi';}catch(_){return false;}}
function hook(){
 const w=typeof unsafeWindow!=='undefined'?unsafeWindow:window;
 try{const f=w.fetch;w.fetch=function(...args){const p=Reflect.apply(f,this,args);if(isBookieURL(args[0]?.url||args[0]))p.then(r=>{if(r.ok)r.clone().json().then(consume).catch(()=>log('Bookie response was not JSON',{},'DEBUG'));},()=>{});return p;};
 const proto=w.XMLHttpRequest.prototype,open=proto.open,send=proto.send,urls=new WeakMap();
 proto.open=function(method,url,...rest){urls.set(this,isBookieURL(url));return Reflect.apply(open,this,[method,url,...rest]);};
 proto.send=function(...args){if(urls.get(this))this.addEventListener('load',function(){try{if(this.status===200)consume(this.responseType==='json'?this.response:JSON.parse(this.responseText));}catch(_){log('Bookie capture unavailable',{},'DEBUG');}},{once:true});return Reflect.apply(send,this,args);};
 log('Passive Bookie response capture installed');}catch(_){log('Response hook unavailable; DOM capture remains active',{},'WARN');}
}
function schedule(){if(!frame)frame=requestAnimationFrame(()=>{frame=0;if(!document.body)return;mount();scanDOM();render();});}
function externalMatch(e){
 const candidates=[...external.values()].filter(x=>Math.abs(stamp(x.commence_time)-e.start)<=5*60000&&[x.home_team,x.away_team].map(norm).sort().join('|')===e.participants.map(norm).sort().join('|'));
 if(candidates.length!==1)return null;
 const x=candidates[0],rows=[];
 for(const b of x.bookmakers||[])for(const m of b.markets||[]){if(m.key!=='h2h')continue;const age=Date.now()-stamp(m.last_update||b.last_update);if(!Number.isFinite(age)||age< -30000||age>TTL)continue;
  const out=m.outcomes||[];if(out.length!==e.outcomes.length||out.some(o=>!Number.isFinite(o.price)||o.price<=1)||out.map(o=>norm(o.name)).sort().join('|')!==e.outcomes.map(o=>norm(o.name)).sort().join('|'))continue;
  rows.push({book:b.title||b.key,outcomes:out,at:m.last_update||b.last_update});
 }
 return rows.length?{x,rows}:null;
}
async function request(path,params={},maxAge=TTL){
 const cacheKey=path+'?'+new URLSearchParams(params);const c=cache.get(cacheKey);if(c&&Date.now()-c.at<maxAge)return c.data;
 const url=new URL('https://api.the-odds-api.com/v4/'+path);for(const [k,v]of Object.entries({...params,apiKey:key}))url.searchParams.set(k,v);
 let response;
 const gm=typeof GM_xmlhttpRequest==='function'?GM_xmlhttpRequest:typeof GM!=='undefined'&&GM.xmlHttpRequest?GM.xmlHttpRequest.bind(GM):null;
 if(gm)response=await new Promise((resolve,reject)=>gm({method:'GET',url:url.href,anonymous:true,timeout:20000,onload:r=>resolve({status:r.status,text:r.responseText}),onerror:()=>reject(new Error('External network request failed')),ontimeout:()=>reject(new Error('External request timed out'))}));
 else{const r=await fetch(url.href,{credentials:'omit',referrerPolicy:'no-referrer',signal:AbortSignal.timeout(20000)});response={status:r.status,text:await r.text()};}
 if(response.status!==200)throw new Error('External provider HTTP '+response.status+'. Check key or quota.');
 let data;try{data=JSON.parse(response.text);}catch(_){throw new Error('Provider returned invalid JSON');}
 if(!Array.isArray(data))throw new Error('Unexpected external response');
 cache.set(cacheKey,{at:Date.now(),data});log('External response',{path,count:data.length});return data;
}
async function loadSports(){if(busy)return;if(!key){note('Enter your The Odds API key in Settings first. No Torn API key is needed.');return;}busy=true;try{catalog=await request('sports/',{},DAY);providerStatus=`${catalog.filter(s=>s.active&&!s.has_outrights).length} active match competitions available. Refresh external odds scans each one, using provider credits.`;render();}catch(e){note(e.message);}finally{busy=false;}}
async function refreshExternal(){
 if(busy)return;if(!key||!catalog.length){note('Save an external key, then click Load external sports first.');return;}
 busy=true;stopped=false;external.clear();let done=0;const sports=catalog.filter(s=>s.active&&!s.has_outrights),from=new Date(),to=new Date(from.getTime()+DAY);
 try{for(const s of sports){if(stopped)break;providerStatus=`External scan ${done}/${sports.length}. Stop is available.`;render();
  const rows=await request('sports/'+encodeURIComponent(s.key)+'/odds/',{regions:cfg.providerRegion,markets:'h2h',oddsFormat:'decimal',dateFormat:'iso',commenceTimeFrom:from.toISOString().replace(/\.\d{3}Z$/,'Z'),commenceTimeTo:to.toISOString().replace(/\.\d{3}Z$/,'Z')});
  for(const x of rows)if(x.id&&x.home_team&&x.away_team)external.set(x.id,x);done++;
 }providerStatus=`External scan ${stopped?'stopped':'finished'}: ${done}/${sports.length} competitions, ${external.size} fixtures. Provider coverage is not every world event.`;
 }catch(e){providerStatus=`Partial external scan ${done}/${sports.length}: ${e.message}`;log('External scan stopped',{completed:done},'WARN');}
 finally{busy=false;render();}
}
function updateOptions(box,values,selected){const sig=JSON.stringify([values,selected]);if(box.dataset.sig===sig)return;box.dataset.sig=sig;box.replaceChildren();for(const [value,label]of values){const o=el('option',label);o.value=value;o.selected=selected.includes(value);box.append(o);}}
function render(){if(!resultBox)return;
 const now=Date.now(),ranked=rankings(now);resultBox.replaceChildren();
 resultBox.append(el('p',`Coverage: ${metadata.size} event records seen; ${events.size} complete markets captured. Torn coverage is PARTIAL. Open sports and expand matches to collect their winner markets.`,'coverage'));
 resultBox.append(el('p',`Next 24 hours. Top five by normalized Torn implied probability. Prices expire after 5 minutes. Estimates are not measured win rates.`));
 for(const [i,q]of ranked.entries()){
  const card=el('article'),a=el('a',`${i+1}. ${q.e.name}`,'match');a.href='https://www.torn.com/page.php?sid=bookie#/'+encodeURIComponent(q.e.sport)+'/'+q.e.id;card.append(a);
  card.append(el('div',q.e.competition+' | '+new Date(q.e.start).toLocaleString()));
  card.append(el('div',`Favorite: ${q.favorite.name} x${q.favorite.odds.toFixed(2)} | Underdog: ${q.underdog.name} x${q.underdog.odds.toFixed(2)}`,'torn'));
  card.append(el('div',`Torn implied estimate: ${(q.p*100).toFixed(1)}% | observed ${new Date(q.e.at).toLocaleTimeString()}`,'torn'));
  const match=externalMatch(q.e);
  if(match){const details=el('details'),summary=el('summary',`External odds: ${match.rows.length} bookmaker(s)`,'web');details.append(summary);
   details.append(el('p','Names, start time and outcome set match. Settlement rules and league identity are not independently verified; these quotes do not change the ranking.','web'));
   for(const row of match.rows){details.append(el('div',`${row.book}: ${row.outcomes.map(o=>o.name+' x'+o.price.toFixed(2)).join(' / ')} | ${new Date(row.at).toLocaleTimeString()}`,'web'));}card.append(details);
  }else card.append(el('div','External odds: no fresh, unambiguous match.','web'));
  resultBox.append(card);
 }
 if(!ranked.length)resultBox.append(el('p','No verified qualifying matches in the captured data. This does not mean there are none elsewhere in Bookie.'));
 resultBox.append(el('p',providerStatus,'web'));
 const sports=[...new Set([...events.values()].map(e=>e.sport))].sort().map(s=>[s,s]);
 updateOptions(sportBox,sports,cfg.sports);const unique=[...new Map([...events.values()].map(e=>[e.id,e])).values()];updateOptions(eventBox,unique.map(e=>[e.id,e.name]),cfg.events);
 root.classList.toggle('mini',cfg.collapsed);clamp();
}
function clamp(){if(!root)return;const w=root.offsetWidth,h=root.offsetHeight;cfg.x=Math.max(0,Math.min(Number(cfg.x)||0,innerWidth-w));cfg.y=Math.max(0,Math.min(Number(cfg.y)||0,innerHeight-Math.min(h,innerHeight)));root.style.left=cfg.x+'px';root.style.top=cfg.y+'px';}
function drag(handle){let d=null,ignore=false;
 handle.addEventListener('pointerdown',e=>{if(e.button!==0||e.target.closest('button')&&e.target!==handle)return;d={id:e.pointerId,x:e.clientX,y:e.clientY,left:cfg.x,top:cfg.y,moved:false};handle.setPointerCapture(e.pointerId);});
 handle.addEventListener('pointermove',e=>{if(!d||d.id!==e.pointerId)return;const dx=e.clientX-d.x,dy=e.clientY-d.y;if(Math.hypot(dx,dy)>5)d.moved=true;if(d.moved){cfg.x=d.left+dx;cfg.y=d.top+dy;clamp();}});
 const end=e=>{if(!d||d.id!==e.pointerId)return;ignore=d.moved;d=null;void put('settings',cfg);};handle.addEventListener('pointerup',end);handle.addEventListener('pointercancel',end);
 handle.addEventListener('click',e=>{if(ignore){e.preventDefault();e.stopImmediatePropagation();ignore=false;}},true);
}
function mount(){
 if(root){if(!root.isConnected)document.body.append(root);return;}
 const style=el('style');style.textContent=`
 #tw-shortlist{position:fixed;width:380px;max-width:calc(100vw - 12px);z-index:2147483638;background:#151c27;color:#e5eaf2;border:1px solid #53647d;border-radius:12px;box-shadow:0 8px 28px #0009;font:13px/1.45 Arial,sans-serif;box-sizing:border-box;overflow:hidden}
 #tw-shortlist *{box-sizing:border-box}#tw-shortlist .bar{display:flex;align-items:center;gap:6px;padding:7px;background:#24334b;touch-action:none;cursor:move;user-select:none}
 #tw-shortlist .bar strong{flex:1}#tw-shortlist button,#tw-shortlist input,#tw-shortlist select{font:inherit;background:#26344a;color:#fff;border:1px solid #718199;border-radius:5px;padding:7px;min-height:40px;max-width:100%}
 #tw-shortlist button{cursor:pointer;touch-action:manipulation}#tw-shortlist .body{padding:10px;max-height:70vh;overflow:auto;overscroll-behavior:contain}
 #tw-shortlist p{margin:7px 0}#tw-shortlist article{padding:10px 0;border-bottom:1px solid #445268}#tw-shortlist .torn{color:#b7b7b7}#tw-shortlist .web{color:#a4d8f4}#tw-shortlist .coverage{color:#f0c67f}
 #tw-shortlist a.match{display:block;color:#0047ab!important;background:#e4edff;padding:6px;border-radius:5px;font-weight:bold;text-decoration:underline;overflow-wrap:anywhere}
 #tw-shortlist label{display:block;margin:10px 0}#tw-shortlist label>*{display:block;width:100%;margin-top:4px}#tw-shortlist .actions{display:flex;flex-wrap:wrap;gap:5px}#tw-shortlist [hidden]{display:none!important}
 #tw-shortlist.mini{width:48px;border-radius:50%;height:48px}#tw-shortlist.mini .body,#tw-shortlist.mini .bar{display:none}#tw-shortlist .token{display:none;width:48px;height:48px;border:0;font-size:25px;touch-action:none}#tw-shortlist.mini .token{display:block}
 #tw-shortlist #tw-shortlist-support{position:static!important;inset:auto!important;width:100%!important;margin-top:12px}#tw-shortlist button:focus-visible{outline:2px solid #a4d8f4}
 `;document.documentElement.append(style);
 root=el('section');root.id='tw-shortlist';root.setAttribute('aria-label','Bookie shortlist');
 const token=button('🎟️',()=>{cfg.collapsed=false;render();void put('settings',cfg);});token.className='token';token.title='Open Bookie shortlist; drag to move';drag(token);
 const bar=el('div',undefined,'bar');bar.append(el('strong','🎟️ Bookie shortlist'),button('⚙️',()=>{settings.open=!settings.open;clamp();}),button('−',()=>{cfg.collapsed=true;render();void put('settings',cfg);}));drag(bar);
 const body=el('div',undefined,'body');statusBox=el('div','Open Bookie matches to capture their markets.');statusBox.setAttribute('role','status');
 const actions=el('div',undefined,'actions');actions.append(button('Recheck captured',()=>{lastDOM='';schedule();}),button('External sports',()=>void loadSports()),button('Refresh external',()=>void refreshExternal()),button('Stop',()=>{stopped=true;}));
 resultBox=el('div');settings=el('details');settings.append(el('summary','Settings and support'));
 const fields={};function field(name,label,type,value){const wrap=el('label',label),n=el('input');n.type=type;n.value=value;n.autocomplete='off';wrap.append(n);settings.append(wrap);fields[name]=n;return n;}
 function select(name,label,options,value){const wrap=el('label',label),n=el('select');for(const [v,t]of options){const o=el('option',t);o.value=v;n.append(o);}n.value=value;wrap.append(n);settings.append(wrap);fields[name]=n;return n;}
 for(const [k,t]of [['min','Favorite minimum multiplier'],['max','Favorite maximum multiplier'],['dog','Underdog minimum multiplier']]){const n=field(k,t,'number',cfg[k]);n.step='0.01';n.min='1.01';}
 select('sex','Event category',[['both','Both, including unknown'],['men','Men only, explicitly identified'],['women','Women only, explicitly identified']],cfg.sex);
 select('region','Country filter (event country, not team nationality)',[['all','All countries, including unknown'],['us','United States'],['country','Specific country'],['international','Outside US, known countries only']],cfg.region);
 field('country','Specific country: two-letter code, e.g. GB, BR','text',cfg.country).maxLength=2;
 sportBox=select('sports','Sports: no selection means ALL captured sports',[],null);sportBox.multiple=true;sportBox.size=4;
 eventBox=select('events','Matches: no selection means ALL captured matches',[],null);eventBox.multiple=true;eventBox.size=4;
 settings.append(button('Select ALL sports and matches',()=>{for(const box of [sportBox,eventBox])for(const o of box.options)o.selected=false;}));
 field('key','The Odds API key (optional, not a Torn key)','password',key);
 select('providerRegion','External bookmaker region (not event country)',[['eu','Europe'],['uk','United Kingdom'],['us','US'],['au','Australia']],cfg.providerRegion);
 const rememberKey=field('remember','Remember external key in userscript storage','checkbox','');rememberKey.checked=false;
 settings.append(el('p','Keys go only to The Odds API. If protected userscript storage is unavailable, the key stays in memory. Settings use local storage as fallback. No bets are placed. No personal betting history is sent.'));
 settings.append(button('Save settings',async()=>{
  const min=Number(fields.min.value),max=Number(fields.max.value),dog=Number(fields.dog.value),country=fields.country.value.trim().toUpperCase();
  if(![min,max,dog].every(x=>Number.isFinite(x)&&x>1&&x<=1e6)||min>max||! /^[A-Z]{2}$/.test(country)){note('Use valid multipliers greater than 1, minimum no larger than maximum, and a two-letter country code.');return;}
  if(busy){note('Stop the external scan before changing settings.');return;}
  cfg={...cfg,min,max,dog,country,sex:fields.sex.value,region:fields.region.value,providerRegion:fields.providerRegion.value,sports:[...sportBox.selectedOptions].map(o=>o.value),events:[...eventBox.selectedOptions].map(o=>o.value)};
  if(key!==fields.key.value.trim()){cache.clear();external.clear();catalog=[];}key=fields.key.value.trim();
  const saved=await put('settings',cfg),secretSaved=await put('key',rememberKey.checked?key:'',true);
  note(saved?'Settings saved.' : 'Settings active for this session; persistent storage failed.');if(rememberKey.checked&&!secretSaved)note('Settings applied. External key is session-only because userscript storage is unavailable.');render();
 }));
 settings.append(button('🪲',()=>MyDebug.toggleView()),button('📋 Copy Logs to Clipboard',function(){void MyDebug.copy(this);}));
 const host=el('div');host.id='tw-shortlist-support-host';settings.append(host);body.append(statusBox,actions,resultBox,settings);root.append(token,bar,body);document.body.append(root);
 support=new SupportModule({containerId:'tw-shortlist-support',styleId:'tw-shortlist-support-css',getParent:()=>host});
 clamp();
}
hook();
async function boot(){
 const stored=await get('settings',{});cfg={...defaults,...stored};
 if(!Array.isArray(cfg.sports))cfg.sports=[];if(!Array.isArray(cfg.events))cfg.events=[];
 if(![cfg.min,cfg.max,cfg.dog].every(x=>Number.isFinite(x)&&x>1)||cfg.min>cfg.max)Object.assign(cfg,{min:1.3,max:2.5,dog:4});
 key=await get('key','',true);if(typeof key!=='string')key='';
 mount();scanDOM();render();
 const observer=new MutationObserver(ms=>{if(!root.isConnected||ms.some(m=>{const n=m.target.nodeType===1?m.target:m.target.parentElement;return !n?.closest('#tw-shortlist,[id^="tw-debug-"]')&&[...m.addedNodes,...m.removedNodes].some(x=>x.nodeType===1||x.nodeType===3)||m.type==='characterData'&&!n?.closest('#tw-shortlist,[id^="tw-debug-"]');}))schedule();});
 observer.observe(document.documentElement,{childList:true,subtree:true,characterData:true});
 window.addEventListener('hashchange',()=>{lastDOM='';schedule();});window.addEventListener('resize',clamp);document.addEventListener('visibilitychange',()=>{if(!document.hidden)schedule();});
 // Expiry-only timer, never used to discover DOM elements or fetch data.
 window.setInterval(()=>{if(!document.hidden)render();},30000);
 log('Ready',{version:'1.0.1',mode:'partial-coverage'});
}
if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',()=>void boot(),{once:true});else void boot();
/*
// @grant        GM_addStyle
// @run-at       document-end
// ==/UserScript==

/*
 * Donation UI Module
 * Version 1.4
 *
 * Reusable support/donation UI for Torn.com userscripts.
 *
 * Features:
 *   - Animated Buy Me a Coffee button
 *   - Animated coffee cup with squash-and-stretch movement
 *   - Animated steam
 *   - Animated coffee fill
 *   - Hover-to-fill coffee effect
 *   - Periodic diagonal button gleam
 *   - Animated liquid-style label transition
 *   - Torn Xanax-tip button
 *   - MutationObserver persistence against Torn/React DOM changes
 *   - TornPDA/mobile-compatible DOM implementation
 *   - Reduced-motion accessibility support
 *
 * License: BSD-3-Clause
 *
 * Copyright (c) 2026 ShavedW00kie
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 *    contributors may be used to endorse or promote products derived from
 *    this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */


// Donation UI v1.4 host adaptation: settings parent, host-managed persistence.
    const DEFAULT_CONFIG = Object.freeze({
        bmcId: "bittick1c",
        tornUserId: "2954173",

        containerId: "thawookie-support-module",
        styleId: "thawookie-support-module-style"
    });

    /*
     * Unique counter used for SVG clipPath IDs.
     *
     * SVG IDs are document-global. If multiple instances of this
     * module are ever created, sharing a clipPath ID can cause one
     * SVG to reference another SVG's clipping path.
     */
    let coffeeInstanceCount = 0;

    /* ============================================================
     * SUPPORT MODULE
     * ============================================================ */

    class SupportModule {
        constructor(config = {}) {
            this.config = {
                ...DEFAULT_CONFIG,
                ...config
            };

            this.observer = null;
            this.observerAttached = false;
            this.isInjecting = false;
            this.destroyed = false;

            this.init();
        }

        /* ========================================================
         * INITIALIZATION
         * ======================================================== */

        init() {
            if (this.destroyed) {
                return;
            }

            if (!this.getBody()) {
                if (document.readyState === "loading") {
                    document.addEventListener(
                        "DOMContentLoaded",
                        () => this.init(),
                        { once: true }
                    );
                }

                return;
            }

            this.injectStyles();
            this.injectUI();
            // Host observer maintains the settings panel.
        }

        /* ========================================================
         * DOM HELPERS
         * ======================================================== */

        getBody() {
            return this.config.getParent?.() || null;
        }

        getContainer() {
            return document.getElementById(
                this.config.containerId
            );
        }

        isContainerConnected() {
            const container = this.getContainer();

            return Boolean(
                container &&
                container.isConnected
            );
        }

        /* ========================================================
         * STYLE INJECTION
         * ======================================================== */

        injectStyles() {
            if (this.destroyed) {
                return;
            }

            if (document.getElementById(this.config.styleId)) {
                return;
            }

            const styles = `
                /* =================================================
                 * DONATION CONTAINER
                 * ================================================= */

                #${this.config.containerId} {
                    position: fixed;
                    bottom: 20px;
                    right: 20px;
                    z-index: 2147483640;
                    display: flex;
                    flex-direction: column;
                    gap: 10px;
                    font-family: Arial, sans-serif;
                    box-sizing: border-box;
                    touch-action: manipulation;
                }

                /* =================================================
                 * GENERIC SUPPORT BUTTON
                 * ================================================= */

                #${this.config.containerId} .tw-support-btn {
                    box-sizing: border-box;
                    display: flex;
                    align-items: center;
                    justify-content: center;
                    min-height: 40px;
                    padding: 10px 15px;
                    border-radius: 8px;
                    font-size: 13px;
                    font-weight: bold;
                    line-height: 1.2;
                    text-align: center;
                    text-decoration: none !important;
                    cursor: pointer;
                    user-select: none;
                    -webkit-tap-highlight-color: transparent;
                    touch-action: manipulation;
                }

                #${this.config.containerId} .tw-support-btn:focus-visible {
                    outline: 2px solid #ffffff;
                    outline-offset: 2px;
                }

                /* =================================================
                 * BUY ME A COFFEE BUTTON
                 *
                 * Visual design ported from the supplied animated
                 * coffee-button implementation:
                 *
                 *   #FFDD00 yellow
                 *   black foreground
                 *   6px radius
                 *   6px 12px compact padding
                 *   11px / 600 typography
                 *   animated glare
                 *   animated cup
                 * ================================================= */

                #${this.config.containerId} .tw-bmc {
                    position: relative;
                    overflow: hidden;
                    isolation: isolate;

                    display: flex;
                    align-items: center;
                    justify-content: center;
                    gap: 6px;

                    width: 100%;
                    min-width: 170px;
                    min-height: 40px;

                    padding: 6px 12px;

                    background: #FFDD00;
                    color: #000000 !important;

                    border: 1px solid #FFDD00;
                    border-radius: 6px;

                    font-size: 11px;
                    font-weight: 600;
                    line-height: 1.2;

                    text-decoration: none !important;

                    box-sizing: border-box;

                    transition:
                        opacity 0.15s ease,
                        transform 0.15s ease;
                }

                /*
                 * Keep all actual button contents above the
                 * animated specular highlight.
                 */
                #${this.config.containerId} .tw-bmc > * {
                    position: relative;
                    z-index: 1;
                }

                /*
                 * Subtle interaction feedback.
                 *
                 * Hover is deliberately opacity-based rather than
                 * relying on desktop-only behavior for functionality.
                 * The button remains fully usable through touch.
                 */
                #${this.config.containerId} .tw-bmc:hover {
                    opacity: 0.9;
                }

                #${this.config.containerId} .tw-bmc:active {
                    transform: scale(0.97);
                }

                /* =================================================
                 * COFFEE CUP - SQUASH & STRETCH
                 * ================================================= */

                @keyframes tw-coffee-cup-hop {
                    0% {
                        transform:
                            translateY(0)
                            scale(1, 1);
                    }

                    18% {
                        transform:
                            translateY(0.5px)
                            scale(1.08, 0.9);
                    }

                    32% {
                        transform:
                            translateY(-2px)
                            scale(0.94, 1.08);
                    }

                    50% {
                        transform:
                            translateY(-3px)
                            scale(1, 1);
                    }

                    68% {
                        transform:
                            translateY(0)
                            scale(1.1, 0.88);
                    }

                    84% {
                        transform:
                            translateY(0)
                            scale(0.97, 1.03);
                    }

                    100% {
                        transform:
                            translateY(0)
                            scale(1, 1);
                    }
                }

                #${this.config.containerId} .tw-coffee-cup {
                    position: relative;
                    display: inline-flex;
                    flex-shrink: 0;

                    transform-origin: 50% 100%;

                    animation:
                        tw-coffee-cup-hop
                        2.4s
                        cubic-bezier(0.4, 0, 0.5, 1)
                        infinite;
                }

                /*
                 * Cup outline remains above the steam.
                 */
                #${this.config.containerId} .tw-coffee-cup > svg {
                    position: relative;
                    z-index: 1;
                    display: block;
                }

                /* =================================================
                 * STEAM
                 * ================================================= */

                #${this.config.containerId} .tw-coffee-cup::before,
                #${this.config.containerId} .tw-coffee-cup::after {
                    content: "";

                    position: absolute;

                    bottom: 74%;

                    width: 2px;
                    height: 4px;

                    border-radius: 999px;

                    background:
                        linear-gradient(
                            to top,
                            rgba(90, 58, 36, 0.5),
                            rgba(90, 58, 36, 0)
                        );

                    opacity: 0;

                    pointer-events: none;

                    will-change:
                        transform,
                        opacity;
                }

                #${this.config.containerId} .tw-coffee-cup::before {
                    left: 27%;

                    animation:
                        tw-coffee-steam
                        2.8s
                        ease-out
                        infinite;
                }

                #${this.config.containerId} .tw-coffee-cup::after {
                    left: 45%;

                    animation:
                        tw-coffee-steam
                        2.8s
                        ease-out
                        infinite;

                    animation-delay: -1.4s;
                }

                @keyframes tw-coffee-steam {
                    0% {
                        opacity: 0;

                        transform:
                            translateY(2px)
                            scale(0.6, 0.5)
                            skewX(0deg);
                    }

                    30% {
                        opacity: 0.7;

                        transform:
                            translateY(0)
                            scale(1, 0.9)
                            skewX(4deg);
                    }

                    65% {
                        opacity: 0.4;

                        transform:
                            translateY(-3px)
                            scale(0.85, 1.2)
                            skewX(-5deg);
                    }

                    100% {
                        opacity: 0;

                        transform:
                            translateY(-5px)
                            scale(0.5, 1.5)
                            skewX(6deg);
                    }
                }

                /* =================================================
                 * COFFEE FILL
                 * ================================================= */

                #${this.config.containerId} .tw-coffee-fill {
                    transform: scaleY(0.15);
                    transform-origin: 50% 100%;

                    animation:
                        tw-coffee-refill
                        7s
                        cubic-bezier(0.45, 0, 0.55, 1)
                        infinite;
                }

                @keyframes tw-coffee-refill {
                    0% {
                        transform: scaleY(0.15);
                    }

                    30% {
                        transform: scaleY(0.95);
                    }

                    55% {
                        transform: scaleY(0.75);
                    }

                    80% {
                        transform: scaleY(0.3);
                    }

                    100% {
                        transform: scaleY(0.15);
                    }
                }

                /*
                 * Hover overrides the normal coffee cycle and fills
                 * the cup completely.
                 */
                #${this.config.containerId}
                .tw-bmc:hover
                .tw-coffee-fill {
                    animation:
                        tw-coffee-fill-to-full
                        0.45s
                        cubic-bezier(0.4, 0, 0.2, 1)
                        forwards;
                }

                @keyframes tw-coffee-fill-to-full {
                    to {
                        transform: scaleY(1);
                    }
                }

                /* =================================================
                 * SPECULAR GLEAM
                 * ================================================= */

                /*
                 * A soft diagonal highlight sweeps across the
                 * yellow button every five seconds.
                 */
                #${this.config.containerId} .tw-bmc::after {
                    content: "";

                    position: absolute;

                    top: 0;
                    bottom: 0;
                    left: -60%;

                    width: 45%;

                    pointer-events: none;

                    background:
                        linear-gradient(
                            100deg,
                            transparent 0%,
                            rgba(255, 255, 255, 0.15) 35%,
                            rgba(255, 255, 255, 0.75) 50%,
                            rgba(255, 255, 255, 0.15) 65%,
                            transparent 100%
                        );

                    transform: skewX(-18deg);

                    will-change: transform;

                    animation:
                        tw-coffee-glare
                        5s
                        cubic-bezier(0.5, 0, 0.5, 1)
                        infinite;
                }

                @keyframes tw-coffee-glare {
                    0% {
                        transform:
                            translateX(0)
                            skewX(-18deg);
                    }

                    22%,
                    100% {
                        transform:
                            translateX(400%)
                            skewX(-18deg);
                    }
                }

                /* =================================================
                 * LIQUID LABEL TRANSITION
                 * ================================================= */

                #${this.config.containerId} .tw-coffee-label {
                    display: grid;
                    align-items: center;
                    justify-items: center;

                    min-width: 0;
                }

                #${this.config.containerId} .tw-coffee-label > span {
                    grid-area: 1 / 1;

                    white-space: nowrap;

                    transform-origin: 50% 50%;

                    will-change:
                        opacity,
                        transform,
                        filter;

                    animation:
                        tw-coffee-label-drip
                        7s
                        cubic-bezier(0.65, 0, 0.35, 1)
                        infinite;
                }

                /*
                 * The second label is exactly 50% out of phase,
                 * creating the alternating liquid transition.
                 */
                #${this.config.containerId}
                .tw-coffee-label
                > span:nth-child(2) {
                    animation-delay: -3.5s;
                }

                @keyframes tw-coffee-label-drip {
                    0%,
                    34% {
                        opacity: 1;

                        transform:
                            translateY(0)
                            scale(1, 1);

                        filter: blur(0);
                    }

                    38% {
                        opacity: 0.5;

                        transform:
                            translateY(2px)
                            scale(0.94, 1.08);

                        filter: blur(1.2px);
                    }

                    42% {
                        opacity: 0;

                        transform:
                            translateY(9px)
                            scale(1.06, 0.5);

                        filter: blur(4px);
                    }

                    42.01%,
                    92% {
                        opacity: 0;

                        transform:
                            translateY(-9px)
                            scale(1.06, 0.5);

                        filter: blur(4px);
                    }

                    96% {
                        opacity: 1;

                        transform:
                            translateY(1px)
                            scale(1.05, 0.9);

                        filter: blur(0);
                    }

                    98% {
                        opacity: 1;

                        transform:
                            translateY(0)
                            scale(0.99, 1.03);

                        filter: blur(0);
                    }

                    100% {
                        opacity: 1;

                        transform:
                            translateY(0)
                            scale(1, 1);

                        filter: blur(0);
                    }
                }

                /* =================================================
                 * TORN TIP BUTTON
                 * ================================================= */

                #${this.config.containerId} .tw-torn-tip {
                    background-color: #8ab63d;
                    color: #ffffff !important;

                    border: 1px solid #6a8c2f;

                    box-shadow:
                        0 4px 6px rgba(0, 0, 0, 0.3);

                    transition:
                        transform 0.2s ease,
                        background-color 0.2s ease;
                }

                #${this.config.containerId} .tw-torn-tip:active {
                    transform: scale(0.95);
                }

                /* =================================================
                 * REDUCED MOTION
                 * ================================================= */

                @media (prefers-reduced-motion: reduce) {
                    #${this.config.containerId}
                    .tw-coffee-cup {
                        animation: none;
                    }

                    #${this.config.containerId}
                    .tw-coffee-cup::before,
                    #${this.config.containerId}
                    .tw-coffee-cup::after {
                        animation: none;
                        opacity: 0;
                    }

                    #${this.config.containerId}
                    .tw-coffee-fill {
                        animation: none;
                        transform: scaleY(0.8);
                    }

                    #${this.config.containerId}
                    .tw-coffee-label > span {
                        animation: none;
                        opacity: 0;
                        filter: none;
                        transform: none;
                    }

                    #${this.config.containerId}
                    .tw-coffee-label
                    > span:nth-child(2) {
                        opacity: 1;
                    }

                    #${this.config.containerId}
                    .tw-bmc::after {
                        animation: none;
                        opacity: 0;
                    }
                }

                /* =================================================
                 * MOBILE / TORN PDA
                 * ================================================= */

                @media (max-width: 480px) {
                    #${this.config.containerId} {
                        right: 10px;
                        bottom: 10px;
                        left: 10px;

                        width: auto;
                    }

                    #${this.config.containerId}
                    .tw-support-btn {
                        width: 100%;
                    }

                    #${this.config.containerId}
                    .tw-bmc {
                        min-width: 0;
                    }
                }
            `;

            /*
             * Preferred Tampermonkey path.
             *
             * Some restricted WebViews can expose GM_addStyle but
             * still throw when it is called. Fall back safely.
             */
            if (false) {
                try {
                    GM_addStyle(styles);
                    return;
                } catch (_) {
                    /*
                     * Fall through to normal DOM style injection.
                     */
                }
            }

            this.injectStyleElement(styles);
        }

        injectStyleElement(styles) {
            if (document.getElementById(this.config.styleId)) {
                return;
            }

            const styleNode =
                document.createElement("style");

            styleNode.id =
                this.config.styleId;

            styleNode.type =
                "text/css";

            styleNode.textContent =
                styles;

            if (document.head) {
                document.head.appendChild(styleNode);
                return;
            }

            const body = this.getBody();

            if (body) {
                body.appendChild(styleNode);
            }
        }

        /* ========================================================
         * COFFEE BUTTON
         * ======================================================== */

        buildCoffeeButton() {
            coffeeInstanceCount += 1;

            const clipId =
                `tw-coffee-clip-${coffeeInstanceCount}`;

            const bmcLink =
                document.createElement("a");

            bmcLink.className =
                "tw-support-btn tw-bmc";

            bmcLink.href =
                `https://www.buymeacoffee.com/${encodeURIComponent(
                    this.config.bmcId
                )}`;

            bmcLink.target = "_blank";

            bmcLink.rel =
                "noopener noreferrer";

            bmcLink.title =
                "Support ThaWookie";

            bmcLink.setAttribute(
                "aria-label",
                "Buy me a coffee - support ThaWookie"
            );

            /*
             * ----------------------------------------------------
             * Animated coffee cup
             * ----------------------------------------------------
             */

            const cup =
                document.createElement("span");

            cup.className =
                "tw-coffee-cup";

            cup.setAttribute(
                "aria-hidden",
                "true"
            );

            const svg =
                document.createElementNS(
                    "http://www.w3.org/2000/svg",
                    "svg"
                );

            svg.setAttribute(
                "width",
                "16"
            );

            svg.setAttribute(
                "height",
                "16"
            );

            svg.setAttribute(
                "viewBox",
                "0 0 24 24"
            );

            svg.setAttribute(
                "fill",
                "none"
            );

            svg.setAttribute(
                "stroke",
                "currentColor"
            );

            svg.setAttribute(
                "stroke-width",
                "1.5"
            );

            svg.setAttribute(
                "aria-hidden",
                "true"
            );

            /*
             * SVG clip path.
             *
             * This is intentionally generated through DOM APIs
             * rather than innerHTML so the only dynamic value,
             * clipId, cannot become an HTML injection vector.
             */

            const defs =
                document.createElementNS(
                    "http://www.w3.org/2000/svg",
                    "defs"
                );

            const clipPath =
                document.createElementNS(
                    "http://www.w3.org/2000/svg",
                    "clipPath"
                );

            clipPath.setAttribute(
                "id",
                clipId
            );

            const clipShape =
                document.createElementNS(
                    "http://www.w3.org/2000/svg",
                    "path"
                );

            clipShape.setAttribute(
                "d",
                "M5 8h11v5a4 4 0 0 1-4 4H9a4 4 0 0 1-4-4V8z"
            );

            clipPath.appendChild(
                clipShape
            );

            defs.appendChild(
                clipPath
            );

            svg.appendChild(
                defs
            );

            /*
             * Coffee liquid.
             *
             * The CSS transform animation controls its visible
             * fill level.
             */
            const coffeeFill =
                document.createElementNS(
                    "http://www.w3.org/2000/svg",
                    "rect"
                );

            coffeeFill.setAttribute(
                "class",
                "tw-coffee-fill"
            );

            coffeeFill.setAttribute(
                "x",
                "5"
            );

            coffeeFill.setAttribute(
                "y",
                "8"
            );

            coffeeFill.setAttribute(
                "width",
                "11"
            );

            coffeeFill.setAttribute(
                "height",
                "9"
            );

            coffeeFill.setAttribute(
                "fill",
                "#6f4e37"
            );

            coffeeFill.setAttribute(
                "stroke",
                "none"
            );

            coffeeFill.setAttribute(
                "clip-path",
                `url(#${clipId})`
            );

            svg.appendChild(
                coffeeFill
            );

            /*
             * Cup body outline.
             */
            const cupBody =
                document.createElementNS(
                    "http://www.w3.org/2000/svg",
                    "path"
                );

            cupBody.setAttribute(
                "stroke-linecap",
                "round"
            );

            cupBody.setAttribute(
                "stroke-linejoin",
                "round"
            );

            cupBody.setAttribute(
                "d",
                "M5 8h11v5a4 4 0 0 1-4 4H9a4 4 0 0 1-4-4V8z"
            );

            svg.appendChild(
                cupBody
            );

            /*
             * Cup handle.
             */
            const cupHandle =
                document.createElementNS(
                    "http://www.w3.org/2000/svg",
                    "path"
                );

            cupHandle.setAttribute(
                "stroke-linecap",
                "round"
            );

            cupHandle.setAttribute(
                "stroke-linejoin",
                "round"
            );

            cupHandle.setAttribute(
                "d",
                "M16 9h2.5a2.5 2.5 0 0 1 0 5H16"
            );

            svg.appendChild(
                cupHandle
            );

            cup.appendChild(
                svg
            );

            bmcLink.appendChild(
                cup
            );

            /*
             * ----------------------------------------------------
             * Animated label
             * ----------------------------------------------------
             */

            const label =
                document.createElement("span");

            label.className =
                "tw-coffee-label";

            label.setAttribute(
                "aria-hidden",
                "true"
            );

            const supportLabel =
                document.createElement("span");

            supportLabel.textContent =
                "Support the project?";

            const coffeeLabel =
                document.createElement("span");

            coffeeLabel.textContent =
                "Buy me a coffee";

            label.appendChild(
                supportLabel
            );

            label.appendChild(
                coffeeLabel
            );

            bmcLink.appendChild(
                label
            );

            return bmcLink;
        }

        /* ========================================================
         * UI INJECTION
         * ======================================================== */

        injectUI() {
            if (
                this.destroyed ||
                this.isInjecting
            ) {
                return;
            }

            const body =
                this.getBody();

            if (!body) {
                return;
            }

            if (this.isContainerConnected()) {
                return;
            }

            this.isInjecting = true;

            try {
                /*
                 * Remove stale disconnected node, if present.
                 */
                const existingContainer =
                    this.getContainer();

                if (existingContainer) {
                    existingContainer.remove();
                }

                const container =
                    document.createElement("div");

                container.id =
                    this.config.containerId;

                container.setAttribute(
                    "role",
                    "complementary"
                );

                container.setAttribute(
                    "aria-label",
                    "Support ThaWookie"
                );

                /*
                 * Animated Buy Me a Coffee button.
                 */
                const bmcLink =
                    this.buildCoffeeButton();

                /*
                 * ------------------------------------------------
                 * Torn Xanax Tip
                 * ------------------------------------------------
                 */

                const tipLink =
                    document.createElement("a");

                tipLink.href =
                    "https://www.torn.com/item.php";

                tipLink.target =
                    "_blank";

                tipLink.rel =
                    "noopener noreferrer";

                tipLink.className =
                    "tw-support-btn tw-torn-tip";

                tipLink.title =
                    `Opens Items - search "Xanax", ` +
                    `tap Send, enter ThaWookie ` +
                    `[${this.config.tornUserId}]`;

                tipLink.setAttribute(
                    "aria-label",
                    `Send a Xanax tip to ThaWookie ` +
                    `[${this.config.tornUserId}]`
                );

                tipLink.textContent =
                    "💊 Send a Xanax Tip";

                /*
                 * Assemble donation controls.
                 */
                container.appendChild(
                    bmcLink
                );

                container.appendChild(
                    tipLink
                );

                /*
                 * Append directly to body so React does not own
                 * the donation UI's DOM subtree.
                 */
                body.appendChild(
                    container
                );
            } finally {
                this.isInjecting = false;
            }
        }

        /* ========================================================
         * MUTATION OBSERVER
         * ======================================================== */

        attachObserver() {
            if (
                this.destroyed ||
                this.observerAttached ||
                typeof MutationObserver === "undefined"
            ) {
                return;
            }

            const body =
                this.getBody();

            if (!body) {
                return;
            }

            this.observer =
                new MutationObserver(
                    (mutationList) => {
                        if (
                            this.destroyed ||
                            this.isInjecting
                        ) {
                            return;
                        }

                        let relevantMutation =
                            false;

                        for (
                            const mutation
                            of mutationList
                        ) {
                            if (
                                mutation.type !==
                                "childList"
                            ) {
                                continue;
                            }

                            if (
                                mutation.removedNodes
                                    .length > 0
                            ) {
                                relevantMutation =
                                    true;

                                break;
                            }
                        }

                        if (
                            !relevantMutation
                        ) {
                            return;
                        }

                        if (
                            !this.isContainerConnected()
                        ) {
                            this.injectStyles();
                            this.injectUI();
                        }
                    }
                );

            this.observer.observe(
                body,
                {
                    childList: true,
                    subtree: true
                }
            );

            this.observerAttached = true;
        }

        /* ========================================================
         * CLEANUP
         * ======================================================== */

        destroy() {
            this.destroyed = true;

            if (this.observer) {
                try {
                    this.observer.disconnect();
                } catch (_) {
                    /*
                     * Nothing further required.
                     */
                }
            }

            this.observer = null;
            this.observerAttached = false;

            const container =
                this.getContainer();

            if (container) {
                container.remove();
            }
        }
    }


/**
 * File: userscript-debugger-module.js
 * Version: 1.0.4
 * Advanced Modular Userscript Debugger with optional DOM Inspector
 * Author: ShavedW00kie (Torn: ThaWookie [2954173] )
 * Namespace: https://github.com/ShavedW00kie/
 * Target: Embedded inside a Torn.com userscript IIFE (desktop and TornPDA).
 * License: BSD-3-Clause
 *
 * Copyright (c) 2026 ShavedW00kie
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * Integration inside the host userscript's IIFE, AFTER this function definition:
 *   const MyDebug = initializeModularDebugger(GM_info.script.name);
 *   MyDebug.log("Ready");
 *   bugButton.addEventListener("click", () => MyDebug.toggleView());
 *   copyButton.addEventListener("click", function () { void MyDebug.copy(this); });
 *   // Optional: MyDebug.inspect(), MyDebug.inspectElement(element),
 *   // MyDebug.watchElement(element), MyDebug.stopInspection(), MyDebug.destroy().
 *
 * This file is a source module, not an independently installable userscript.
 * The host userscript supplies its own ==UserScript== metadata and IIFE.
 */
function initializeModularDebugger(scriptNamespace) {
    "use strict";
    if (scriptNamespace === undefined) scriptNamespace = "App";

    const randomId = (() => {
        try {
            if (typeof crypto !== "undefined" && crypto.randomUUID) {
                return crypto.randomUUID().replace(/-/g, "");
            }
        } catch (_) { /* WebView fallback. */ }
        return Math.random().toString(36).slice(2) + Date.now().toString(36);
    })();
    const id = `tw-debug-${randomId}`;
    const LIMITS = Object.freeze({
        buffer: (10 * 1024 * 1024) - (900 * 1024),
        entry: 64 * 1024,
        renderEntries: 180,
        renderChars: 128 * 1024,
        report: 15000,
        html: 6000,
        parents: 6,
        children: 12,
        nodes: 65,
        mutations: 40
    });
    const state = {
        logs: [], head: 0, length: 0, destroyed: false, 
        frames: new Set(), statuses: new Map(), resizeObserver: null,
        root: null, logArea: null, inspector: null, inspectorText: null,
        style: null, statusBar: null, highlight: null,
        panelMode: "logs", selected: null, picking: false,
        watching: false, changeLog: [],
        observer: null, parentObserver: null, uiObserver: null,
        observedBody: null, renderPending: false,
        pendingMutations: 0, mutationLogPending: false,
        viewportListeners: false, highlightPending: false
    };
    const SENSITIVE = /(?:^key$|api[_-]?key|apikey|token|auth|authorization|cookie|secret|passwd|password|csrf|session|bearer|credential|client[_-]?secret|refresh[_-]?token|access[_-]?token)/i;
    const SAFE_ATTRIBUTES = new Set([
        "id", "class", "role", "type", "aria-expanded",
        "aria-hidden", "data-testid", "data-test", "data-role", "data-state"
    ]);

    /* ---------- Redacted, bounded logging ---------- */
    function redact(value) {
        return String(value)
            .replace(/\b(?:Authorization|Proxy-Authorization)\s*:\s*[^\r\n]+/gi, "Authorization: [REDACTED]")
            .replace(/\b[A-Za-z0-9]{16}\b/g, "[POSSIBLE KEY REDACTED]")
            // Bearer tokens and known secret-bearing URL parameters.
            .replace(/(\bBearer\s+)[A-Za-z0-9._~+/-]+/gi, "$1[REDACTED]")
            .replace(/([?&](?:key|api_key|token|access_token|refresh_token|secret|session|csrf)=)[^&#\s\"'<>}\]]+/gi, "$1[REDACTED]")
            // Quoted property values, including embedded spaces.
            .replace(/(["']?(?:api[_-]?key|apikey|token|authorization|cookie|password|passwd|secret|csrf|session|access[_-]?token|refresh[_-]?token)["']?\s*[:=]\s*)(["'])([^"']*)\2/gi,
                (_, prefix, quote) => `${prefix}${quote}[REDACTED]${quote}`)
            // Unquoted key=value patterns.
            .replace(/(["']?(?:api[_-]?key|apikey|token|authorization|cookie|password|passwd|secret|csrf|session|access[_-]?token|refresh[_-]?token)["']?\s*[:=]\s*)(?!["'])([^\s"',;}&\]]+)/gi,
                (_, prefix) => `${prefix}[REDACTED]`);
    }

    // Does not call getters or toJSON. Proxies can still execute traps; never
    // deliberately pass hostile proxies to an in-process diagnostic function.
    function safeSerialize(value) {
        let remaining = 240;
        const path = new WeakSet();
        function visit(item, depth) {
            if (--remaining < 0) return "[Traversal limit]";
            if (typeof item === "string") return redact(item.slice(0, 8192));
            if (item === null || typeof item === "boolean" || typeof item === "number") return item;
            if (typeof item === "undefined") return "[undefined]";
            if (typeof item === "bigint" || typeof item === "symbol") return String(item);
            if (typeof item === "function") return "[Function]";
            if (path.has(item)) return "[Circular]";
            if (depth >= 5) return "[Depth limit]";
            path.add(item);
            try {
                const result = Object.create(null);
                let count = 0;
                if (item instanceof Error) {
                    for (const key of ["name", "message", "stack"]) {
                        const descriptor = Object.getOwnPropertyDescriptor(item, key);
                        result[key] = descriptor && "value" in descriptor
                            ? visit(descriptor.value, depth + 1) : "[Unavailable/accessor]";
                    }
                }
                // for-in permits early exit without allocating Object.keys for
                // every property. Reflection itself is not a hard time limit.
                for (const key in item) {
                    if (!Object.prototype.hasOwnProperty.call(item, key)) continue;
                    if (++count > 40 || remaining <= 0) { result["[Truncated]"] = true; break; }
                    const descriptor = Object.getOwnPropertyDescriptor(item, key);
                    result[redact(key.slice(0, 160))] = SENSITIVE.test(key) ? "[REDACTED]"
                        : descriptor && "value" in descriptor ? visit(descriptor.value, depth + 1) : "[Accessor omitted]";
                }
                return result;
            } catch (_) { return "[Unserializable]"; }
            finally { path.delete(item); }
        }
        try {
            if (typeof value === "string") return redact(value.slice(0, LIMITS.entry));
            return JSON.stringify(visit(value, 0));
        } catch (_) { return "[Unserializable]"; }
    }
    function scheduleFrame(callback) {
        if (state.destroyed) return;
        if (typeof requestAnimationFrame !== "function") { callback(); return; }
        const handle = requestAnimationFrame(() => {
            state.frames.delete(handle);
            if (!state.destroyed) callback();
        });
        state.frames.add(handle);
    }
    function trim(text, max) {
        text = String(text);
        return text.length > max ? `${text.slice(0, Math.max(0, max - 17))}[TRUNCATED]` : text;
    }
    function log(message, level = "INFO") {
        if (state.destroyed) return;
        const label = typeof level === "string" && /^(INFO|WARN|ERROR|DEBUG)$/i.test(level) ? level.toUpperCase() : "INFO";
        const timestamp = new Date().toISOString();
        const entry = trim(`[${timestamp}] [${label}] ${safeSerialize(message)}`, LIMITS.entry);
        const size = entry.length + 1;
        while (state.head < state.logs.length && state.length + size > LIMITS.buffer) {
            state.length -= state.logs[state.head].length + 1;
            state.logs[state.head++] = null; // Release pruned strings immediately.
        }
        if (state.head > 2048) { state.logs = state.logs.slice(state.head); state.head = 0; }
        state.logs.push(entry);
        state.length += size;
        queueRender();
    }
    const info = message => log(message, "INFO");
    const warn = message => log(message, "WARN");
    const error = message => log(message, "ERROR");
    function clear() {
        state.logs.length = 0;
        state.head = 0;
        state.length = 0;
        renderLogs();
    }
    function queueRender() {
        if (!state.logArea || !state.root || state.root.hidden || state.panelMode !== "logs") return;
        if (state.renderPending) return;
        state.renderPending = true;
        scheduleFrame(() => { state.renderPending = false; renderLogs(); });
    }
    function renderLogs() {
        if (state.destroyed || !state.root || state.root.hidden || !state.logArea || !state.logArea.isConnected || state.panelMode !== "logs") return;
        const subset = [];
        let chars = 0;
        for (let i = state.logs.length - 1; i >= state.head && subset.length < LIMITS.renderEntries; i--) {
            if (chars + state.logs[i].length + 1 > LIMITS.renderChars) break;
            subset.unshift(state.logs[i]); chars += state.logs[i].length + 1;
        }
        const skipped = state.logs.length - state.head - subset.length;
        state.logArea.textContent = (skipped ? `[${skipped} earlier entries retained for copying]\n` : "") + subset.join("\n");
        state.logArea.scrollTop = state.logArea.scrollHeight;
    }

    /* ---------- Clipboard (Tampermonkey, TornPDA, browser) ---------- */
    function copyFallback(text) {
        if (!document.body) return false;
        const input = document.createElement("textarea");
        const previousFocus = document.activeElement;
        const selection = typeof window.getSelection === "function" ? window.getSelection() : null;
        const ranges = [];
        if (selection) for (let i = 0; i < selection.rangeCount; i++) ranges.push(selection.getRangeAt(i).cloneRange());
        let caret = null;
        try { if (previousFocus && typeof previousFocus.selectionStart === "number") caret = [previousFocus.selectionStart, previousFocus.selectionEnd, previousFocus.selectionDirection]; } catch (_) {}
        input.value = text;
        input.readOnly = true;
        input.style.cssText = "position:fixed;left:0;top:0;width:1px;height:1px;opacity:0;z-index:-1";
        try {
            document.body.appendChild(input);
            input.focus();
            input.select();
            input.setSelectionRange(0, text.length);
            return Boolean(document.execCommand("copy"));
        } catch (_) { return false; }
        finally {
            input.remove();
            try { if (previousFocus && previousFocus.isConnected) previousFocus.focus({ preventScroll: true });
                if (caret) previousFocus.setSelectionRange(...caret);
                if (selection) { selection.removeAllRanges(); ranges.forEach(range => selection.addRange(range)); } } catch (_) { /* Non-focusable element. */ }
        }
    }
    async function writeClipboard(text) {
        try {
            if (typeof GM_setClipboard === "function") {
                await Promise.resolve(GM_setClipboard(text, "text"));
                return true;
            }
            if (typeof GM !== "undefined" && typeof GM.setClipboard === "function") {
                await GM.setClipboard(text, "text");
                return true;
            }
        } catch (_) { /* Try browser APIs. */ }
        if (typeof navigator !== "undefined" && navigator.clipboard && navigator.clipboard.writeText) {
            try { await navigator.clipboard.writeText(text); return true; }
            catch (_) { /* Restricted WebView. */ }
        }
        return copyFallback(text);
    }
    function showCopyResult(button, result) {
        if (state.destroyed || !button || !button.isConnected) return;
        let saved = state.statuses.get(button);
        if (saved) clearTimeout(saved.timer);
        else saved = { nodes: Array.from(button.childNodes), timer: null };
        button.textContent = result;
        // This timer is only UI feedback, never element discovery or polling.
        saved.timer = setTimeout(() => {
            button.replaceChildren(...saved.nodes);
            state.statuses.delete(button);
        }, 1300);
        state.statuses.set(button, saved);
    }
    async function copy(button = null) {
        if (state.destroyed) return false;
        const text = state.logs.slice(state.head).join("\n");
        if (!text) { showCopyResult(button, "Empty"); return false; }
        const success = await writeClipboard(text);
        showCopyResult(button, success ? "Copied!" : "Failed");
        if (!success) warn("Clipboard unavailable. Open debugger to select and copy manually.");
        return success;
    }

    /* ---------- Safe DOM descriptions ---------- */
    function isElement(node) { return Boolean(node && node.nodeType === 1 && node.tagName); }
    function tag(node) { return isElement(node) ? node.tagName.toLowerCase() : "(none)"; }
    function describe(node) {
        if (!isElement(node)) return "(none)";
        let text = tag(node);
        const nodeId = node.getAttribute("id");
        if (nodeId && !SENSITIVE.test(nodeId)) text += `#${trim(redact(nodeId), 50)}`;
        const classes = Array.from(node.classList || []).filter(name => !SENSITIVE.test(name)).slice(0, 3);
        if (classes.length) text += "." + classes.map(name => trim(redact(name), 48)).join(".");
        return trim(text, 180);
    }
    function selectorSegment(node) {
        if (!isElement(node)) return "";
        const nodeId = node.getAttribute("id");
        if (nodeId && /^[A-Za-z_][\w-]{0,60}$/.test(nodeId) && !SENSITIVE.test(nodeId)) {
            return `#${nodeId}`;
        }
        let part = tag(node);
        const classNames = Array.from(node.classList || [])
            .filter(name => /^[A-Za-z_][\w-]{0,45}$/.test(name) && !SENSITIVE.test(name))
            .slice(0, 2);
        part += classNames.map(name => `.${name}`).join("");
        if (node.parentElement) {
            const same = Array.from(node.parentElement.children).filter(sibling => sibling.tagName === node.tagName);
            if (same.length > 1) part += `:nth-of-type(${same.indexOf(node) + 1})`;
        }
        return part;
    }
    function makeSelector(element) {
        const segments = [];
        let current = element;
        for (let step = 0; step < LIMITS.parents && isElement(current); step++) {
            const segment = selectorSegment(current);
            segments.unshift(segment);
            if (segment.startsWith("#")) break;
            current = current.parentElement;
        }
        const selector = segments.join(" > ");
        if (selector.length > 500) return "(selector exceeds safe length)";
        if (redact(selector) !== selector) return "(selector omitted: possible credential)";
        return selector;
    }
    function safeAttributeText(element) {
        const result = [];
        if (!isElement(element)) return "";
        for (const attr of Array.from(element.attributes || [])) {
            if (!SAFE_ATTRIBUTES.has(attr.name) || SENSITIVE.test(attr.name)) continue;
            if (SENSITIVE.test(attr.value)) continue;
            result.push(`${attr.name}="${escapeHTML(trim(redact(attr.value), 90))}"`);
            if (result.length >= 8) break;
        }
        return result.length ? ` ${result.join(" ")}` : "";
    }
    function escapeHTML(value) {
        return String(value).replace(/[&<>"']/g, character => ({
            "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"
        })[character]);
    }
    function structuralHTML(element) {
        let budget = LIMITS.nodes;
        const skip = /^(script|style|noscript|template|iframe|object|embed)$/i;
        function recurse(node, depth) {
            if (!isElement(node) || budget-- <= 0) return "";
            const name = tag(node);
            const open = `<${name}${safeAttributeText(node)}>`;
            if (skip.test(name)) return `${open}[contents omitted]</${name}>`;
            if (depth >= 2) return `${open}[descendants omitted]</${name}>`;
            const kids = Array.from(node.children).slice(0, LIMITS.children);
            const nested = kids.map(child => recurse(child, depth + 1)).join("\n");
            const note = node.children.length > LIMITS.children ? "\n[additional children omitted]" : "";
            return `${open}${nested ? `\n${nested}${note}\n` : "[text omitted]"}</${name}>`;
        }
        return trim(recurse(element, 0), LIMITS.html);
    }
    function reactRootHint(element) {
        let node = element;
        for (let i = 0; i < LIMITS.parents && isElement(node); i++, node = node.parentElement) {
            const candidateId = node.getAttribute("id") || "";
            if (/^(?:react-root|root|__next)$/i.test(candidateId) || node.hasAttribute("data-reactroot")) {
                return `${describe(node)} (heuristic only)`;
            }
        }
        return "Not detected (does not rule out React)";
    }
    function getInspectionReport() {
        const element = state.selected;
        if (!isElement(element)) return "No element selected.";
        const ancestors = [];
        let ancestor = element.parentElement;
        for (let i = 0; i < LIMITS.parents && isElement(ancestor); i++, ancestor = ancestor.parentElement) {
            ancestors.push(`  ${i + 1}. ${describe(ancestor)}`);
        }
        const children = Array.from(element.children).slice(0, LIMITS.children)
            .map((child, index) => `  ${index + 1}. ${describe(child)}`);
        const page = typeof location !== "undefined"
            ? (location.origin === "null" ? "(local document)" : `${location.origin}${location.pathname}`)
            : "(unknown)";
        return trim(redact([
            `DOM INSPECTION | ${redact(String(scriptNamespace))}`,
            `Time: ${new Date().toISOString()}`,
            `Page (query omitted): ${redact(page)}`,
            `Selected: ${describe(element)}`,
            `Connected: ${element.isConnected}`,
            `Selector (best effort): ${makeSelector(element)}`,
            `React container hint: ${reactRootHint(element)}`,
            `Parent chain:\n${ancestors.join("\n") || "  (none)"}`,
            `Immediate children (${element.children.length}):\n${children.join("\n") || "  (none)"}`,
            `Sibling context: previous=${describe(element.previousElementSibling)}, next=${describe(element.nextElementSibling)}`,
            `Structural preview (text nodes, form values, URLs and scripts omitted; review attributes before sharing):\n${structuralHTML(element)}`,
            `Recent observed mutations (${state.changeLog.length}):\n${state.changeLog.join("\n") || "  (none)"}`
        ].join("\n\n")), LIMITS.report);
    }

    /* ---------- On-demand DOM selection and mutation watch ---------- */
    function isOurUI(node) {
        return Boolean(isElement(node) && (
            (state.root && state.root.contains(node)) ||
            (state.highlight && state.highlight.contains(node))
        ));
    }
    function ensureHighlight() {
        if (state.destroyed || !state.selected || !state.root || state.root.hidden || state.panelMode !== "inspect") return null;
        if (state.highlight && state.highlight.isConnected) return state.highlight;
        if (!document.body) return null;
        const node = document.createElement("div");
        node.setAttribute("aria-hidden", "true");
        node.style.cssText = "position:fixed;pointer-events:none;z-index:2147483646;border:2px solid #00dbff;box-shadow:0 0 0 1px #001e28;box-sizing:border-box;display:none";
        document.body.appendChild(node);
        state.highlight = node;
        return node;
    }
    function updateHighlight() {
        const marker = ensureHighlight();
        if (!marker) return;
        const node = state.selected;
        if (!isElement(node) || !node.isConnected || !state.root || state.root.hidden || state.panelMode !== "inspect") {
            marker.style.display = "none";
            return;
        }
        const rect = node.getBoundingClientRect();
        marker.style.display = "block";
        marker.style.top = `${rect.top}px`;
        marker.style.left = `${rect.left}px`;
        marker.style.width = `${rect.width}px`;
        marker.style.height = `${rect.height}px`;
    }
    function onViewportChanged() {
        if (state.destroyed || !state.selected || state.highlightPending || state.panelMode !== "inspect") return;
        state.highlightPending = true;
        scheduleFrame(() => {
            state.highlightPending = false;
            updateHighlight();
        });
    }
    function setViewportListeners(enable) {
        if (typeof window === "undefined" || enable === state.viewportListeners) return;
        state.viewportListeners = enable;
        const method = enable ? "addEventListener" : "removeEventListener";
        window[method]("scroll", onViewportChanged, true);
        window[method]("resize", onViewportChanged);
    }
    function removeHighlight() {
        if (state.highlight) { state.highlight.remove(); state.highlight = null; }
    }
    function updateInspector() {
        if (!state.inspectorText) return;
        state.inspectorText.textContent = state.selected ? trim([
            `Selected: ${describe(state.selected)}`,
            `Parent: ${describe(state.selected.parentElement)}`,
            `Children: ${state.selected.children.length}`,
            `Selector: ${makeSelector(state.selected)}`,
            `Connected: ${state.selected.isConnected}`,
            `Watch: ${state.watching ? "ON" : "OFF"} | Changes: ${state.changeLog.length}`
        ].join("\n"), 1100) : "Tap Pick, then tap a Torn page element.\nNo page data is collected until inspection is used.";
        if (state.statusBar) state.statusBar.textContent = state.picking ? "PICK MODE: tap a page element or press Esc" : "Inspector idle";
        updateHighlight();
    }
    function suppressPickAction(event) {
        if (isOurUI(event.target)) return;
        event.stopImmediatePropagation();
        // Preserve the browser synthetic click needed for tap selection.
    }
    function onPickClick(event) {
        if (isOurUI(event.target)) return;
        // Capture before Torn/React click handlers so selecting a link does not navigate.
        event.preventDefault();
        event.stopImmediatePropagation();
        if (isElement(event.target)) inspectElement(event.target);
        stopPicker();
    }
    function onPickKey(event) {
        if (event.key === "Escape") {
            event.preventDefault();
            stopPicker();
            updateInspector();
        }
    }
    function startPicker() {
        if (state.destroyed || !state.root || !state.root.isConnected || state.root.hidden || state.picking) return;
        state.picking = true;
        document.addEventListener("click", onPickClick, true);
        ["pointerdown", "pointerup", "touchstart", "touchend", "mousedown", "mouseup"].forEach(type => document.addEventListener(type, suppressPickAction, { capture: true, passive: false }));
        document.addEventListener("keydown", onPickKey, true);
        updateInspector();
    }
    function stopPicker() {
        if (!state.picking) return;
        state.picking = false;
        document.removeEventListener("click", onPickClick, true);
        ["pointerdown", "pointerup", "touchstart", "touchend", "mousedown", "mouseup"].forEach(type => document.removeEventListener(type, suppressPickAction, true));
        document.removeEventListener("keydown", onPickKey, true);
        updateInspector();
    }
    function stopWatch() {
        if (state.observer) state.observer.disconnect();
        if (state.parentObserver) state.parentObserver.disconnect();
        state.observer = null;
        state.parentObserver = null;
        state.watching = false;
        state.pendingMutations = 0;
        updateInspector();
    }
    function handleMutations(mutations) {
        if (!state.watching) return;
        const stamp = new Date().toISOString();
        let changed = 0;
        for (const mutation of mutations) {
            if (changed >= 8) break;
            const detail = mutation.type === "characterData" ? "text node changed (content omitted)" : mutation.type === "attributes"
                ? `attribute ${mutation.attributeName} on ${describe(mutation.target)}`
                : `childList (+${mutation.addedNodes.length}/-${mutation.removedNodes.length}) on ${describe(mutation.target)}`;
            state.changeLog.push(`[${stamp}] ${detail}`);
            changed++;
        }
        while (state.changeLog.length > LIMITS.mutations) state.changeLog.shift();
        if (changed) {
            state.pendingMutations += changed;
            if (!state.mutationLogPending) {
                state.mutationLogPending = true;
                scheduleFrame(() => {
                    state.mutationLogPending = false;
                    const count = state.pendingMutations;
                    state.pendingMutations = 0;
                    if (count && state.watching) log(`DOM watch: ${count} sampled change(s) near ${describe(state.selected)}`, "DEBUG");
                });
            }
        }
        if (state.selected && !state.selected.isConnected) {
            warn(`DOM watch: selected element detached: ${describe(state.selected)}`);
            stopWatch();
        }
        updateInspector();
    }
    function watchElement(element = state.selected) {
        if (state.destroyed || !isElement(element) || !element.isConnected || element === document.documentElement || element === document.body) {
            warn("DOM watch requires a specific element, not the document root/body.");
            return false;
        }
        if (typeof MutationObserver === "undefined") {
            warn("MutationObserver is unavailable in this WebView.");
            return false;
        }
        stopWatch();
        if (element !== state.selected && !inspectElement(element)) return false;
        state.changeLog.length = 0;
        // Observe the chosen subtree and direct child lists along its ancestor chain.
        state.observer = new MutationObserver(handleMutations);
        state.observer.observe(element, {
            attributes: true, childList: true, characterData: true, subtree: true,
            attributeFilter: ["class", "id", "role", "aria-expanded", "hidden", "disabled", "data-state"]
        });
        if (element.parentElement) {
            state.parentObserver = new MutationObserver(handleMutations);
            let ancestor = element.parentElement;
            while (ancestor) {
                state.parentObserver.observe(ancestor, { childList: true });
                ancestor = ancestor.parentNode;
            }
        }
        state.watching = true;
        info(`DOM watch enabled: ${describe(element)}`);
        updateInspector();
        return true;
    }
    function moveSelection(direction) {
        const selected = state.selected;
        if (!isElement(selected)) return;
        const next = direction === "parent" ? selected.parentElement : selected.firstElementChild;
        if (next && next !== document.body && next !== document.documentElement) inspectElement(next);
    }
    function inspectElement(element) {
        if (state.destroyed || !isElement(element) || isOurUI(element) || !ensureUI()) return false;
        if (state.watching && state.selected !== element) stopWatch();
        state.selected = element;
        if (state.resizeObserver) state.resizeObserver.disconnect();
        if (typeof ResizeObserver === "function") {
            state.resizeObserver = new ResizeObserver(onViewportChanged);
            state.resizeObserver.observe(element);
        }
        state.changeLog.length = 0;
        showPanel("inspect");
        updateInspector();
        info(`DOM selected: ${describe(element)} | ${makeSelector(element)}`);
        return true;
    }
    function inspect() {
        if (!showPanel("inspect")) return false;
        startPicker();
        return true;
    }
    function stopInspection() {
        stopPicker();
        stopWatch();
        state.selected = null;
        if (state.resizeObserver) state.resizeObserver.disconnect();
        state.resizeObserver = null;
        state.changeLog.length = 0;
        removeHighlight();
        setViewportListeners(false);
        if (state.root && !state.root.hidden) showPanel("logs");
    }
    async function copyInspection(button = null) {
        if (state.destroyed) return false;
        if (!state.selected) { showCopyResult(button, "No selection"); return false; }
        const result = await writeClipboard(getInspectionReport());
        showCopyResult(button, result ? "Copied!" : "Failed");
        return result;
    }

    /* ---------- Compact UI, created on first use ---------- */
    function createButton(text, label, handler) {
        const button = document.createElement("button");
        button.type = "button";
        button.textContent = text;
        button.title = label;
        button.setAttribute("aria-label", label);
        button.className = `${id}-btn`;
        button.addEventListener("click", handler);
        return button;
    }
    function ensureStyles() {
        if (state.destroyed) return;
        if (state.style && state.style.isConnected) return;
        if (!document.head && !document.body) return;
        const style = document.createElement("style");
        style.id = `${id}-styles`;
        style.textContent = `
          @keyframes ${id}-reset {from{opacity:.7}to{opacity:1}}
          .${id}-flash{animation:${id}-reset 1.3s ease 1}
          #${id}{position:fixed;right:12px;bottom:12px;width:min(430px,calc(100vw - 24px));
            height:320px;max-height:70vh;display:flex;flex-direction:column;gap:8px;padding:10px;
            background:#191919;color:#e2ffe7;border:1px solid #46db85;border-radius:8px;
            box-shadow:0 6px 25px #0009;box-sizing:border-box;font:12px/1.45 monospace;
            z-index:2147483647;touch-action:manipulation}
          #${id}[hidden],#${id} [hidden]{display:none!important}
          #${id} button{font:11px/1.2 sans-serif;min-height:30px;cursor:pointer}
          #${id} .${id}-btn{border:1px solid #616161;border-radius:4px;background:#292929;
            color:#fff;padding:6px;touch-action:manipulation}
          #${id} .${id}-toolbar{display:flex;flex-wrap:wrap;align-items:center;gap:4px}
          #${id} .${id}-title{font-weight:bold;flex:1 1 120px;min-width:0;overflow:hidden;text-overflow:ellipsis}
          #${id} .${id}-body{flex:1;min-height:0;overflow:auto;white-space:pre-wrap;
            overflow-wrap:anywhere;user-select:text}
          #${id} .${id}-actions{display:flex;flex-wrap:wrap;gap:5px;margin-bottom:5px}
          #${id} .${id}-status{font-size:11px;color:#ace3fc}
          #${id} button:focus-visible{outline:2px solid #91dfff;outline-offset:2px}
          @media(max-width:480px){#${id}{right:8px;bottom:8px;width:calc(100vw - 16px);
            height:290px;font-size:11px}}
          @media(prefers-reduced-motion:reduce){.${id}-flash{animation:none}}
        `;
        (document.head || document.body).appendChild(style);
        state.style = style;
    }
    function ensureUI() {
        if (state.destroyed) return false;
        if (state.root && state.root.isConnected) { ensureStyles(); return true; }
        if (!document.body) return false;
        ensureStyles();
        const root = document.createElement("section");
        root.id = id;
        root.hidden = true;
        root.setAttribute("aria-label", `Debug console: ${String(scriptNamespace)}`);
        const toolbar = document.createElement("div");
        toolbar.className = `${id}-toolbar`;
        const title = document.createElement("span");
        title.className = `${id}-title`;
        title.textContent = `🪲 ${String(scriptNamespace)}`;
        toolbar.append(title,
            createButton("Copy", "Copy logs", function () { void copy(this); }),
            createButton("Clear", "Clear logs", clear),
            createButton("🔍", "Inspect Torn DOM element", inspect),
            createButton("Hide", "Hide debugger", () => toggleView()));
        const logArea = document.createElement("pre");
        logArea.className = `${id}-body`;
        logArea.style.margin = "0";
        const inspector = document.createElement("div");
        inspector.className = `${id}-body`;
        inspector.hidden = true;
        const actions = document.createElement("div");
        actions.className = `${id}-actions`;
        actions.append(
            createButton("Pick", "Pick element by tapping it", startPicker),
            createButton("↑ Parent", "Inspect parent element", () => moveSelection("parent")),
            createButton("↓ Child", "Inspect first child element", () => moveSelection("child")),
            createButton("Watch", "Watch selected element for DOM mutations", () => { watchElement(); }),
            createButton("Stop watch", "Disconnect mutation observers", stopWatch),
            createButton("Copy DOM", "Copy sanitized DOM report", function () { void copyInspection(this); }),
            createButton("Exit", "Close inspector", stopInspection));
        const status = document.createElement("div");
        status.className = `${id}-status`;
        const details = document.createElement("pre");
        details.style.cssText = "white-space:pre-wrap;overflow-wrap:anywhere;margin:5px 0;font:inherit";
        inspector.append(actions, status, details);
        root.append(toolbar, logArea, inspector);
        document.body.appendChild(root);
        Object.assign(state, { root, logArea, inspector, inspectorText: details, statusBar: status });
        attachUIObserver();
        return true;
    }
    function attachUIObserver() {
        if (typeof MutationObserver === "undefined" || !document.body) return;
        if (state.uiObserver) state.uiObserver.disconnect();
        // Only direct children of body, not the constantly changing React subtree.
        state.uiObserver = new MutationObserver(() => {
            if (state.root && (!state.root.isConnected || state.observedBody !== document.body)) {
                stopPicker();
                stopWatch();
                removeHighlight();
                setViewportListeners(false);
                if (state.root) state.root.remove();
                if (state.resizeObserver) state.resizeObserver.disconnect();
                state.resizeObserver = null;
                state.selected = null;
                state.root = state.logArea = state.inspector = state.inspectorText = state.statusBar = null;
                state.uiObserver.disconnect();
            }
        });
        state.uiObserver.observe(document.body, { childList: true });
        if (document.documentElement) state.uiObserver.observe(document.documentElement, { childList: true });
        state.observedBody = document.body;
    }
    function showPanel(panel) {
        if (!ensureUI()) return false;
        state.root.hidden = false;
        state.panelMode = panel;
        setViewportListeners(panel === "inspect");
        state.logArea.hidden = panel !== "logs";
        state.inspector.hidden = panel !== "inspect";
        if (panel === "logs") renderLogs();
        else updateInspector();
        return true;
    }
    function toggleView() {
        if (!ensureUI()) return false;
        if (!state.root.hidden) {
            // A hidden debugger must not keep an active DOM picker or watch.
            stopInspection();
            state.root.hidden = true;
            return false;
        }
        showPanel("logs");
        return true;
    }

    function destroy() {
        if (state.destroyed) return;
        state.destroyed = true;
        stopInspection();
        if (state.uiObserver) state.uiObserver.disconnect();
        if (state.resizeObserver) state.resizeObserver.disconnect();
        for (const handle of state.frames) {
            if (typeof cancelAnimationFrame === "function") cancelAnimationFrame(handle);
        }
        state.frames.clear();
        for (const [button, saved] of state.statuses) {
            clearTimeout(saved.timer);
            button.replaceChildren(...saved.nodes);
        }
        state.statuses.clear();
        if (state.root) state.root.remove();
        if (state.style) state.style.remove();
        removeHighlight();
        state.root = state.logArea = state.inspector = state.inspectorText = state.statusBar = state.style = null;
        clear();
    }

    return Object.freeze({
        log, info, warn, error, copy, clear, toggleView,
        inspect, inspectElement, watchElement, stopInspection,
        getInspectionReport, copyInspection, destroy
    });
}

})(typeof GM_info !== 'undefined' ? GM_info : null);
