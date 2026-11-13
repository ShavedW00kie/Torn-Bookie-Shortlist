// ==UserScript==
// @name         Torn_Bookie_Shortlist
// @namespace    https://github.com/ShavedW00kie/
// @version      1.0.2
// @description  Compact 24-hour Bookie shortlist, partial coverage and optional external odds with key testing.
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
const VERSION = '1.0.2';
const GM_info = {...(nativeInfo || {}), script: {...(nativeInfo?.script || {}), name: 'Torn_Bookie_Shortlist', version: VERSION}};
const MyDebug = initializeModularDebugger(GM_info.script.name);
/*
Install: replace the previous script in Tampermonkey or TornPDA, save, and reload
https://www.torn.com/page.php?sid=bookie. Drag the header or collapsed ticket.

v1.0.2: independent external key setup; fresh key test and quota feedback;
conditional country validation; compact cards and grouped settings; preserved
draft selections; state-change capture logs; no freshness extension from clocks.
Donation UI v1.4 and debugger v1.0.4 are embedded below with their licenses.

Coverage remains PARTIAL. This script passively reads loaded Bookie markets.
Open sports and expand matches to capture them. No automatic all-event feed is
claimed. Only exhaustive two-participant 2-Way Full event / 3-Way Ordinary time
markets are accepted. Races, outrights and unknown market scopes are excluded.
Country means explicit event-country metadata, never participant nationality.
Men/women-only filters exclude events whose category is not explicitly labeled.

Ranking uses (1/favorite odds) / sum(1/all outcome odds), including the draw.
This is an implied estimate, not a measured win rate. Draw cannot satisfy the
opponent threshold. Favorite/underdog filters use Torn's decimal multipliers.

External setup: Settings > External odds > Save & test key. The sports catalog
test uses /v4/sports/ and no odds credits. Check external odds then scans active
match competitions, one h2h market and one bookmaker region per request.
Up to one credit per uncached competition; Stop ends after the current request.
Requests are manual, sequential and cached: catalog 24 hours, odds 5 minutes.
Names are accent-normalized; sport family, starts within 5 minutes and identical
outcome sets are required. Ambiguous fixtures and stale quotes are excluded.
League and settlement equivalence are unverified. External quotes do not change
the ranking. No performance statistics or probabilities are invented.

No Torn API key is needed. Optional external keys go only to The Odds API, and
persist only in userscript storage if Remember is checked. They never enter
localStorage or logs. Preferences can use localStorage. No bets are placed.
No private betting history is collected or sent. Live TornPDA testing is needed.
*/
const PREFIX = 'tw-shortlist-v1:', TTL = 5 * 60000, DAY = 86400000;
const defaults = {min:1.3,max:2.5,dog:4,sex:'both',region:'all',country:'',sports:[],events:[],collapsed:false,x:12,y:90,providerRegion:'eu'};
let cfg = {...defaults}, key = '', root, uiStyle, body, home, settings, resultBox, statusBox, coverageBox, coverageDetails;
let keyStatusBox, providerBox, providerSettingsBox, sportBox, eventBox, filterStatusBox, externalSettings, rememberBox;
let externalButton, stopButton, testButton, gearButton, support;
let busy=false, stopped=false, frame=0, catalog=[], quota={}, providerStatus='External: not checked.', keyStatus='No key saved.', lastRender='';
let externalLoaded=false, scanComplete=false, prefsWrite=Promise.resolve(), lastCaptureSummary='', lastExternalRequestAt=0;
const fields={}, events=new Map(), external=new Map(), metadata=new Map(), cache=new Map(), cardSignatures=new WeakMap(), seenIDs=new Set();
let visibleCards=0, expandedCards=0;
const norm=s=>String(s??'').normalize('NFD').replace(/[\u0300-\u036f]/g,'').toLowerCase().replace(/[^a-z0-9]+/g,' ').trim();
const txt=n=>(n?.textContent||'').replace(/\s+/g,' ').trim();
const stamp=v=>{const n=Number(v);return Number.isFinite(n)&&n>1e9?(n<1e11?n*1000:n):typeof v==='string'&&/(Z|[+-]\d\d:\d\d)$/.test(v)?Date.parse(v):NaN;};
const log=(event,extra={},level='INFO')=>MyDebug.log({event,...extra},level);
async function get(k,d,secret=false){
 const readers=[];if(typeof GM_getValue==='function')readers.push(()=>GM_getValue(PREFIX+k,d));
 if(typeof GM!=='undefined'&&typeof GM.getValue==='function')readers.push(()=>GM.getValue(PREFIX+k,d));
 if(!secret)readers.push(()=>JSON.parse(localStorage.getItem(PREFIX+k)||'null')??d);
 for(const read of readers)try{return (await read())??d;}catch(_){log('Storage read failed',{item:k},'WARN');}return d;
}
async function put(k,v,secret=false){
 const writers=[];if(typeof GM_setValue==='function')writers.push(()=>GM_setValue(PREFIX+k,v));
 if(typeof GM!=='undefined'&&typeof GM.setValue==='function')writers.push(()=>GM.setValue(PREFIX+k,v));
 if(!secret)writers.push(()=>localStorage.setItem(PREFIX+k,JSON.stringify(v)));
 for(const write of writers)try{await write();return true;}catch(_){log('Storage write failed',{item:k},'WARN');}return false;
}
function savePrefs(){const snapshot=JSON.parse(JSON.stringify(cfg));prefsWrite=prefsWrite.then(()=>put('settings',snapshot));return prefsWrite;}
function el(tag,text,cls){const n=document.createElement(tag);if(text!==undefined)n.textContent=text;if(cls)n.className=cls;return n;}
function button(label,fn){const b=el('button',label);b.type='button';b.addEventListener('click',fn);return b;}
function text(n,s){if(n&&n.textContent!==s)n.textContent=s;}
function note(s){if(statusBox){text(statusBox,s);statusBox.hidden=!s;}}
function route(hash){const m=String(hash).match(/^#\/([a-z0-9-]+)\/(\d+)\/?$/i);return m?{sport:m[1],id:m[2]}:null;}
function validMarket(e){
 if(!e||!/^\d+$/.test(e.id)||!e.sport||!Number.isFinite(e.start)||!Array.isArray(e.participants)||e.participants.length!==2||!Array.isArray(e.outcomes))return false;
 if(!['2-Way Full event','3-Way Ordinary time'].includes(e.market))return false;
 const names=e.outcomes.map(o=>norm(o.name));
 if(names.length!==(e.market.startsWith('3')?3:2)||new Set(names).size!==names.length)return false;
 if(e.participants.some(p=>!norm(p)||!names.includes(norm(p)))||new Set(e.participants.map(norm)).size!==2)return false;
 if(names.length===3&&!names.includes('draw'))return false;
 return e.outcomes.every(o=>o.name&&Number.isFinite(o.odds)&&o.odds>1&&o.odds<=1e6&&!o.suspended);
}
function gender(e){const s=norm(e.competition+' '+e.name);if(/\b(women|womens|female|ladies|wnba|wta)\b/.test(s))return 'women';if(/\b(men|mens|male|atp)\b/.test(s))return 'men';return 'unknown';}
function qualifying(e,now=Date.now()){
 if(!validMarket(e)||!Number.isFinite(e.at)||e.start<=now||e.start>now+DAY||now-e.at>TTL||e.at>now+30000)return null;
 if(cfg.sports.length&&!cfg.sports.includes(e.sport))return null;
 if(cfg.events.length&&!cfg.events.includes(e.id))return null;
 if(cfg.sex!=='both'&&gender(e)!==cfg.sex)return null;
 if(cfg.region!=='all'&&(!e.country||(cfg.region==='international'?e.country==='US':e.country!==(cfg.region==='us'?'US':cfg.country))))return null;
 const teams=e.outcomes.filter(o=>e.participants.some(p=>norm(p)===norm(o.name))).sort((a,b)=>a.odds-b.odds);
 if(teams.length!==2||teams[0].odds===teams[1].odds||teams[0].odds<cfg.min||teams[0].odds>cfg.max||teams[1].odds<cfg.dog)return null;
 if(e.outcomes.some(o=>o.odds<teams[0].odds))return null;
 return {e,favorite:teams[0],underdog:teams[1],p:(1/teams[0].odds)/e.outcomes.reduce((s,o)=>s+1/o.odds,0)};
}
function rankings(now=Date.now()){
 const best=new Map();for(const e of events.values()){const q=qualifying(e,now);if(q&&(!best.has(e.id)||best.get(e.id).p<q.p))best.set(e.id,q);}
 return [...best.values()].sort((a,b)=>b.p-a.p||a.e.start-b.e.start||a.e.id.localeCompare(b.e.id)).slice(0,5);
}
function marketSignature(e){return JSON.stringify([e.id,e.sport,e.start,e.country,e.competition,e.participants,e.market,e.outcomes]);}
function remember(e){
 const k=e.id+'|'+e.market,previous=events.get(k);
 if(!validMarket(e)){if(events.delete(k))log('Market invalidated',{id:e.id,market:e.market},'WARN');return;}
 events.set(k,e);seenIDs.add(e.id);
 if(!previous||marketSignature(previous)!==marketSignature(e))log(previous?'Market updated':'Market captured',{id:e.id,sport:e.sport,outcomes:e.outcomes.length});
}
function dateFromDOM(card){
 for(const n of [card,...card.querySelectorAll('[data-start-timestamp],[data-start-time],[data-start],time[datetime],[title]')]){
  for(const a of ['data-start-timestamp','data-start-time','data-start','datetime','title']){const s=n.getAttribute(a);if(!s)continue;const t=stamp(s);if(Number.isFinite(t))return t;
   const m=s.match(/^(?:Due to start at|Starts at)\s*(\d{1,2}):(\d{2})(?::(\d{2}))?\s*(?:-|on)\s*(\d{1,2})\/(\d{1,2})\/(\d{4})(?:\s*(?:TCT|UTC|GMT))?$/i);
   if(m){const t=Date.UTC(+m[6],+m[5]-1,+m[4],+m[1],+m[2],+(m[3]||0)),d=new Date(t);if(d.getUTCMonth()===+m[5]-1&&d.getUTCDate()===+m[4]&&d.getUTCHours()===+m[1]&&d.getUTCMinutes()===+m[2])return t;}
  }
 }return NaN;
}
function clean(n){if(!n)return '';const c=n.cloneNode(true);c.querySelectorAll('.label,.tbma-inline').forEach(x=>x.remove());return txt(c);}
function scanDOM(){
 const cards=[...new Set([...document.querySelectorAll('.matchName .name p')].map(p=>p.closest('li')).filter(Boolean))];
 visibleCards=cards.length;expandedCards=0;
 for(const card of cards){
  const r=(card.classList.contains('active')?route(location.hash):null)||[...card.querySelectorAll('a[href]')].map(a=>{try{return route(new URL(a.href,location.href).hash);}catch(_){return null;}}).find(Boolean);
  if(!r)continue;seenIDs.add(r.id);
  const p=card.querySelector('.matchName .name p'),participants=[...p.querySelectorAll('b')].map(txt),meta=metadata.get(r.id)||{},start=dateFromDOM(card);
  const e={...r,name:participants.join(' v '),participants,competition:txt(p).replace(/^.*?\s-\s/,''),start:Number.isFinite(start)?start:meta.start,country:meta.country||'',at:Date.now()};
  if(participants.length!==2)continue;
  const markets=[];
  for(const ul of card.querySelectorAll('ul.bets-wrap')){
   let m=null;
   for(const li of ul.children){if(!li.classList.contains('bets'))continue;const h=li.querySelector('.market-name-cell');
    if(h){m={market:txt(h.querySelector('.bold')),outcomes:[]};markets.push(m);continue;}
    if(!m)continue;const c=li.querySelector('.cells-wrap'),dest=c?.querySelector('.result'),o=c?.querySelector('.odds.decimal'),input=c?.querySelector('input.amount');
    if(!dest||!o)continue;m.outcomes.push({name:txt(dest.querySelector('span'))||txt(dest),odds:Number(clean(o).replace(/^x\s*/i,'')),suspended:!!input?.disabled||/suspended/i.test(input?.value||'')});
   }
  }
  const supported=markets.filter(m=>['2-Way Full event','3-Way Ordinary time'].includes(m.market));
  if(supported.length)expandedCards++;
  const disabled=card.classList.contains('disabled')||card.getAttribute('aria-disabled')==='true';
  // Clock text and unrelated widgets must never renew a price's timestamp.
  const signature=JSON.stringify([r.id,r.sport,e.start,e.country,e.competition,participants,disabled,supported]);
  if(cardSignatures.get(card)===signature)continue;cardSignatures.set(card,signature);
  if(disabled){for(const [k,v]of events)if(v.id===r.id&&events.delete(k))log('Market disabled',{id:r.id},'WARN');continue;}
  for(const m of supported)remember({...e,...m});
 }
 const summary={visibleCards,expandedCards,capturedMarkets:events.size,seenEvents:new Set([...seenIDs,...metadata.keys()]).size};
 const sig=JSON.stringify(summary);if(sig!==lastCaptureSummary){lastCaptureSummary=sig;log('Capture summary',summary);}
}
function updateMetadata(m){
 if(!m?.ID)return;const id=String(m.ID),previous=metadata.get(id)||{},start=stamp(m.startTimestamp);
 metadata.set(id,{start:Number.isFinite(start)?start:previous.start,country:/^[A-Za-z]{2}$/.test(m.countryCode||'')?m.countryCode.toUpperCase():previous.country||''});
}
function consume(data){
 if(!data||typeof data!=='object')return;
 const payload=[data,data.data,data.response].find(x=>x&&(Array.isArray(x.gameBoxesList)||Array.isArray(x.outcomeTypes)))||data;
 for(const box of Array.isArray(payload.gameBoxesList)?payload.gameBoxesList:[])for(const m of Array.isArray(box.matches)?box.matches:[])updateMetadata(m);
 const m=payload.match;
 if(m?.ID){updateMetadata(m);const id=String(m.ID),sport=String(m.alias||'');
  for(const market of Array.isArray(payload.outcomeTypes)?payload.outcomeTypes:[]){const name=String(market.name||market.outcome||'');if(!['2-Way Full event','3-Way Ordinary time'].includes(name))continue;
   const e={id,sport,name:String(m.name||''),competition:String(m.competition||''),participants:(Array.isArray(m.ep)?m.ep:[]).map(p=>String(p.name||'')),...metadata.get(id),market:name,at:Date.now(),outcomes:(Array.isArray(market.odds)?market.odds:[]).map(o=>({name:String(o.bettingoffer||o.label||''),odds:Number(o.odds),suspended:o.betIsAllowed!==true||o.active===false||Number(o.is_live)===1||/suspend|closed/i.test(String(o.state||''))}))};
   if(/^[a-z]+(?:-[a-z0-9]+)*$/.test(sport))remember(e);
  }
 }schedule();
}
function isBookieURL(value){try{const u=new URL(String(value),location.href);return u.origin===location.origin&&u.pathname==='/page.php'&&u.searchParams.get('sid')==='bookieApi';}catch(_){return false;}}
function hook(){
 const w=typeof unsafeWindow!=='undefined'?unsafeWindow:window;
 try{const f=w.fetch;if(typeof f==='function')w.fetch=function(...args){const p=Reflect.apply(f,this,args);if(isBookieURL(args[0]?.url||args[0]))p.then(r=>{if(r.ok)r.clone().json().then(consume).catch(()=>log('Bookie response was not JSON',{},'DEBUG'));},()=>{});return p;};
 const proto=w.XMLHttpRequest.prototype,open=proto.open,send=proto.send,urls=new WeakMap();
 proto.open=function(method,url,...rest){urls.set(this,isBookieURL(url));return Reflect.apply(open,this,[method,url,...rest]);};
 proto.send=function(...args){if(urls.get(this))this.addEventListener('load',function(){try{if(this.status===200)consume(this.responseType==='json'?this.response:JSON.parse(this.responseText));}catch(_){log('Bookie capture unavailable',{},'DEBUG');}},{once:true});return Reflect.apply(send,this,args);};
 log('Passive Bookie response capture installed');}catch(_){log('Response hook unavailable; DOM capture remains active',{},'WARN');}
}
function schedule(){if(!frame)frame=requestAnimationFrame(()=>{frame=0;if(!document.body)return;mount();scanDOM();render();});}
function sportFamily(s){const n=norm(s).replace(/ /g,'');return ({football:'soccer',soccer:'soccer',americanfootball:'americanfootball',basketball:'basketball',baseball:'baseball',icehockey:'icehockey',tennis:'tennis',cricket:'cricket',mma:'mma',mixedmartialarts:'mma',boxing:'boxing',rugbyleague:'rugbyleague',rugbyunion:'rugbyunion',aussierules:'aussierules'})[n]||'';}
function externalMatch(e){
 const family=sportFamily(e.sport);if(!family)return null;
 const candidates=[...external.values()].filter(x=>String(x.sport_key).startsWith(family+'_')&&Math.abs(stamp(x.commence_time)-e.start)<=5*60000&&[x.home_team,x.away_team].map(norm).sort().join('|')===e.participants.map(norm).sort().join('|'));
 if(candidates.length!==1)return null;
 const x=candidates[0],rows=[];
 for(const b of x.bookmakers||[])for(const m of b.markets||[]){if(m.key!=='h2h')continue;const age=Date.now()-stamp(m.last_update||b.last_update);if(!Number.isFinite(age)||age< -30000||age>TTL)continue;
  const out=m.outcomes||[];if(out.length!==e.outcomes.length||out.some(o=>!Number.isFinite(o.price)||o.price<=1)||out.map(o=>norm(o.name)).sort().join('|')!==e.outcomes.map(o=>norm(o.name)).sort().join('|'))continue;
  rows.push({book:b.title||b.key,outcomes:out,at:m.last_update||b.last_update});
 }return rows.length?{x,rows}:null;
}
function quotaText(){return Number.isFinite(quota.remaining)?`${quota.remaining} credits remaining`:'';}
function readQuota(headers){
 for(const [field,name]of [['remaining','x-requests-remaining'],['used','x-requests-used'],['last','x-requests-last']]){
  const value=typeof headers?.get==='function'?headers.get(name):String(headers||'').match(new RegExp('(?:^|\\r?\\n)'+name+':\\s*(\\d+)','i'))?.[1];
  if(value!==undefined&&value!==null&&/^\d+$/.test(String(value)))quota[field]=Number(value);
 }
}
function providerError(status,data){
 const code=data&&typeof data==='object'?data.error_code:'';
 const known={MISSING_KEY:'The external provider did not receive a key.',INVALID_KEY:'The Odds API key is invalid or not associated with a subscription.',DEACTIVATED_KEY:'The Odds API key has been deactivated.',OUT_OF_USAGE_CREDITS:'The external account has no usage credits remaining.',EXCEEDED_FREQ_LIMIT:'The external provider rate limit was reached. Try again later.',INVALID_REGION:'The provider rejected the bookmaker region.',INVALID_MARKET:'The provider does not support the requested market.',INVALID_MARKET_COMBO:'This competition does not support head-to-head odds.',UNKNOWN_SPORT:'The external competition is no longer available.',INVALID_SPORT:'The external competition identifier was rejected.'};
 if(Object.prototype.hasOwnProperty.call(known,code))return known[code];
 if(status===401)return 'Key rejected (HTTP 401). Recheck your The Odds API key.';
 if(status===402)return 'External quota unavailable (HTTP 402). Check your provider account.';
 if(status===403)return 'Provider denied access (HTTP 403). Check your key and account.';
 if(status===429)return 'Provider rate limit or quota reached (HTTP 429). Scan stopped; try later.';
 if(!status)return 'No external response. Check your connection and TornPDA cross-domain request support.';
 return `External provider returned HTTP ${status}. The scan stopped.`;
}
async function request(path,params={},maxAge=TTL,force=false,cacheID=''){
 const cacheKey=cacheID||path+'?'+new URLSearchParams(params),c=cache.get(cacheKey);
 if(!force&&c&&Date.now()-c.at<maxAge&&(!params.commenceTimeTo||stamp(c.windowTo)>=Date.now()+DAY)){log('External cache used',{path,count:c.data.length},'DEBUG');return c.data;}
 // Provider request pacing only. No timer is used to wait for page content.
 const delay=Math.max(0,250-(Date.now()-lastExternalRequestAt));if(delay)await new Promise(resolve=>setTimeout(resolve,delay));lastExternalRequestAt=Date.now();
 const url=new URL('https://api.the-odds-api.com/v4/'+path);for(const [k,v]of Object.entries({...params,apiKey:key}))url.searchParams.set(k,v);
 log('External request started',{path,region:params.regions||null});
 try{
  const gm=typeof GM_xmlhttpRequest==='function'?GM_xmlhttpRequest:typeof GM!=='undefined'&&typeof GM.xmlHttpRequest==='function'?GM.xmlHttpRequest.bind(GM):null;
  let response;
  if(gm)response=await new Promise((resolve,reject)=>{
   let done=false,handle;const finish=(error,r)=>{if(done)return;done=true;clearTimeout(timer);error?reject(error):resolve({status:r.status,text:r.responseText??r.response,headers:r.responseHeaders});};
   // Network watchdog only, never used for DOM discovery.
   const timer=setTimeout(()=>{finish(new Error('External request timed out after 20 seconds.'));try{handle?.abort?.();}catch(_){}},20000);
   try{handle=gm({method:'GET',url:url.href,anonymous:true,timeout:20000,onload:r=>finish(null,r),onerror:()=>finish(new Error(providerError(0))),ontimeout:()=>finish(new Error('External request timed out after 20 seconds.')),onabort:()=>finish(new Error('External request was cancelled.'))});
    if(handle&&typeof handle.then==='function')handle.then(r=>{if(r&&typeof r==='object'&&'status'in r)finish(null,r);},()=>finish(new Error(providerError(0))));
   }catch(_){finish(new Error(providerError(0)));}
  });
  else{
   const controller=new AbortController(),timer=setTimeout(()=>controller.abort(),20000);
   try{const r=await fetch(url.href,{credentials:'omit',referrerPolicy:'no-referrer',signal:controller.signal});response={status:r.status,text:await r.text(),headers:r.headers};}
   catch(_){throw new Error(controller.signal.aborted?'External request timed out after 20 seconds.':providerError(0));}finally{clearTimeout(timer);}
  }
  readQuota(response.headers);
  let data;try{data=typeof response.text==='string'?JSON.parse(response.text):response.text;}catch(_){if(response.status!==200)throw new Error(providerError(response.status));throw new Error('External provider returned invalid JSON.');}
  if(response.status!==200)throw new Error(providerError(response.status,data));
  if(!Array.isArray(data))throw new Error('External provider returned an unexpected response.');
  cache.set(cacheKey,{at:Date.now(),windowTo:params.commenceTimeTo,data});log('External response',{path,status:response.status,count:data.length,...quota});return data;
 }catch(e){log('External request failed',{path,reason:e.message},'WARN');throw e;}
}
async function activateKey(){
 const entered=fields.key.value.trim();if(!entered)throw new Error('Paste your The Odds API key in External odds settings.');
 if(/[\s\u0000-\u001f\u007f]/.test(entered)||entered.length>256)throw new Error('The key contains spaces or invalid characters. Paste only the key.');
 if(entered!==key){cache.clear();external.clear();catalog=[];quota={};externalLoaded=false;scanComplete=false;key=entered;}
 if(cfg.providerRegion!==fields.providerRegion.value){external.clear();externalLoaded=false;scanComplete=false;cfg.providerRegion=fields.providerRegion.value;}
 fields.key.value=key;
 const saved=await put('key',rememberBox.checked?key:'',true);await savePrefs();
 return rememberBox.checked?(saved?'Key saved.':'Key active for this session; protected storage unavailable.'):(saved?'Key active for this session.':'Key active for this session; any older saved key could not be cleared.');
}
function setBusy(value){busy=value;for(const n of [testButton,externalButton,fields.key,fields.providerRegion,rememberBox])if(n)n.disabled=value;if(stopButton){stopButton.hidden=!value;stopButton.disabled=stopped;}render();}
async function loadSports(){
 if(busy)return;stopped=false;setBusy(true);note('');
 try{keyStatus='Testing key...';render();const saved=await activateKey();catalog=await request('sports/',{},DAY,true);
  const count=catalog.filter(s=>s.active&&!s.has_outrights).length;keyStatus=`Key verified. ${saved}`;providerStatus=`${count} active competitions. ${quotaText()||'Quota headers unavailable.'}`;
  log('External key verified',{competitions:count,...quota});
 }catch(e){keyStatus=e.message;providerStatus='External setup needs attention.';}
 finally{setBusy(false);}
}
async function refreshExternal(){
 if(busy)return;stopped=false;setBusy(true);note('');let done=0,sports=[];
 try{
  const saved=await activateKey();catalog=await request('sports/',{},DAY);keyStatus=`Key verified. ${saved}`;
  sports=catalog.filter(s=>s.active&&!s.has_outrights&&typeof s.key==='string');
  if(stopped){providerStatus='External scan stopped before odds requests.';return;}
  if(!sports.length){providerStatus='No active external match competitions were returned.';return;}
  external.clear();externalLoaded=false;scanComplete=false;
  for(const s of sports){
   if(stopped)break;const cacheID=`odds:${s.key}:${cfg.providerRegion}`,cached=cache.get(cacheID);
   if(quota.remaining===0&&!(cached&&Date.now()-cached.at<TTL))throw new Error('No external credits remaining. Scan stopped.');
   providerStatus=`Checking external odds: ${done}/${sports.length} competitions`;render();
   // Extra TTL at the end makes cached responses cover the whole next-24h window.
   const from=Date.now(),rows=await request('sports/'+encodeURIComponent(s.key)+'/odds/',{regions:cfg.providerRegion,markets:'h2h',oddsFormat:'decimal',dateFormat:'iso',commenceTimeFrom:new Date(from).toISOString().replace(/\.\d{3}Z$/,'Z'),commenceTimeTo:new Date(from+DAY+TTL).toISOString().replace(/\.\d{3}Z$/,'Z')},TTL,false,cacheID);
   for(const x of rows)if(x&&x.id&&x.home_team&&x.away_team)external.set(x.id,{...x,sport_key:x.sport_key||s.key});
   externalLoaded=true;done++;
  }
  scanComplete=!stopped&&done===sports.length;
  providerStatus=`External ${scanComplete?'checked':'stopped'}: ${done}/${sports.length} competitions, ${external.size} fixtures.`;
  log('External scan finished',{completed:done,total:sports.length,fixtures:external.size,partial:!scanComplete,...quota});
 }catch(e){providerStatus=`External scan stopped (${done}/${sports.length}): ${e.message}`;keyStatus=done?keyStatus:e.message;log('External scan stopped',{completed:done,total:sports.length},'WARN');
  if(!key){showSettings(true);externalSettings.open=true;}
 }finally{setBusy(false);}
}
function updateOptions(box,values,selected){
 const sig=JSON.stringify(values);if(box.dataset.options===sig)return;
 const chosen=box.dataset.options===undefined?selected:[...box.selectedOptions].map(o=>o.value);
 // Preserve unsaved choices, including temporarily absent options.
 const prior=new Map([...box.options].map(o=>[o.value,o.textContent]));
 for(const value of chosen)if(!values.some(v=>v[0]===value))values.push([value,prior.get(value)||value]);
 box.dataset.options=JSON.stringify(values);box.replaceChildren();
 for(const [value,label]of values){const o=el('option',label);o.value=value;o.selected=chosen.includes(value);box.append(o);}
}
function unmatchedLabel(){return !externalLoaded?(busy?'External: checking...':'External: not checked.'):(scanComplete?'External: no fresh matching quote.':'External: no match in loaded data.');}
function render(){
 if(!root)return;const now=Date.now(),ranked=rankings(now),matched=ranked.map(q=>externalMatch(q.e));
 const seen=new Set([...seenIDs,...metadata.keys()]).size,fresh=[...events.values()].filter(e=>now-e.at<=TTL&&e.start>now).length;
 text(coverageBox,`${fresh} fresh markets · ${seen} events seen · PARTIAL`);
 text(coverageDetails,`${events.size} complete markets captured this session; ${visibleCards} cards currently loaded, ${expandedCards} with winner markets expanded. Open sports and expand matches to collect more. Capture is partial, never all Torn events. Prices expire after 5 minutes. Reopen a market to observe it again.`);
 text(keyStatusBox,keyStatus);
 text(providerBox,providerStatus);
 const count=catalog.filter(s=>s.active&&!s.has_outrights).length;
 text(providerSettingsBox,[providerStatus,quotaText(),count?`A full scan can cost up to ${count} credits before cached responses. Key tests use no odds credits.`:'Key testing loads the sports catalog without using odds credits.'].filter(Boolean).join(' '));
 const sig=JSON.stringify([ranked,matched,unmatchedLabel()]);
 if(sig!==lastRender){
  lastRender=sig;const opened=new Set([...resultBox.querySelectorAll('details[open]')].map(n=>n.dataset.event));resultBox.replaceChildren();
  for(const [i,q]of ranked.entries()){
   const card=el('article'),a=el('a',`${i+1}. ${q.e.name}`,'twsl-match');a.href='https://www.torn.com/page.php?sid=bookie#/'+encodeURIComponent(q.e.sport)+'/'+q.e.id;card.append(a);
   card.append(el('div',`${q.favorite.name} x${q.favorite.odds.toFixed(2)} · Opponent x${q.underdog.odds.toFixed(2)}`,'twsl-torn'));
   card.append(el('div',`${(q.p*100).toFixed(1)}% Torn implied · ${new Date(q.e.start).toLocaleString(undefined,{weekday:'short',hour:'2-digit',minute:'2-digit'})}`,'twsl-torn'));
   const match=matched[i];card.append(el('div',match?`External: ${match.rows.length} matching bookmaker${match.rows.length===1?'':'s'}.`:unmatchedLabel(),'twsl-web'));
   const details=el('details');details.dataset.event=q.e.id;details.open=opened.has(q.e.id);details.append(el('summary','Details and quotes'));
   details.append(el('div',q.e.competition),el('div',`Starts: ${new Date(q.e.start).toLocaleString()} (device time)`),el('div',`Opponent: ${q.underdog.name} x${q.underdog.odds.toFixed(2)}`,'twsl-torn'),el('div',`Observed: ${new Date(q.e.at).toLocaleTimeString()} · ${q.e.market}`,'twsl-torn'));
   if(match){for(const row of match.rows)details.append(el('p',`${row.book}: ${row.outcomes.map(o=>o.name+' x'+o.price.toFixed(2)).join(' / ')} · ${new Date(row.at).toLocaleTimeString()}`,'twsl-web'));
    details.append(el('p','Sport, names, start and outcome set match. League and settlement equivalence are unverified; external quotes do not change ranking.','twsl-web'));
   }else details.append(el('p','External coverage can omit competitions. Name differences, ambiguous fixtures, stale prices or different outcome sets also prevent a match.','twsl-web'));
   card.append(details);resultBox.append(card);
  }
  if(!ranked.length)resultBox.append(el('p',fresh?'No captured markets meet your filters.':'Open a Bookie match to capture a fresh winner market.'));
 }
 const unique=[...new Map([...events.values()].map(e=>[e.id,e])).values()];
 updateOptions(sportBox,[...new Set(unique.map(e=>e.sport))].sort().map(s=>[s,s]),cfg.sports);
 updateOptions(eventBox,unique.map(e=>[e.id,e.name]),cfg.events);
 root.dataset.twslView=cfg.collapsed?'collapsed':'expanded';clamp();
}
function clamp(){if(!root)return;const viewport=window.visualViewport,w=viewport?.width||innerWidth,h=viewport?.height||innerHeight;
 cfg.x=Math.max(0,Math.min(Number(cfg.x)||0,w-root.offsetWidth));cfg.y=Math.max(0,Math.min(Number(cfg.y)||0,h-Math.min(root.offsetHeight,h)));root.style.left=cfg.x+'px';root.style.top=cfg.y+'px';}
function drag(handle){let d=null,ignore=false;
 handle.addEventListener('pointerdown',e=>{if(e.button!==0||e.target.closest('button')&&e.target!==handle)return;ignore=false;d={id:e.pointerId,x:e.clientX,y:e.clientY,left:cfg.x,top:cfg.y,moved:false};try{handle.setPointerCapture(e.pointerId);}catch(_){} });
 handle.addEventListener('pointermove',e=>{if(!d||d.id!==e.pointerId)return;const dx=e.clientX-d.x,dy=e.clientY-d.y;if(Math.hypot(dx,dy)>5)d.moved=true;if(d.moved){cfg.x=d.left+dx;cfg.y=d.top+dy;clamp();}});
 const end=e=>{if(!d||d.id!==e.pointerId)return;ignore=d.moved;d=null;void savePrefs();};handle.addEventListener('pointerup',end);handle.addEventListener('pointercancel',end);
 handle.addEventListener('click',e=>{if(ignore){e.preventDefault();e.stopImmediatePropagation();ignore=false;}},true);
}
function showSettings(open){settings.hidden=!open;home.hidden=open;gearButton.setAttribute('aria-expanded',String(open));body.scrollTop=0;clamp();}
function field(parent,name,label,type,value){
 const wrap=el('label',label),n=el('input');n.type=type;n.id='twsl-'+name;n.value=value;n.autocomplete='off';wrap.htmlFor=n.id;wrap.append(n);parent.append(wrap);fields[name]=n;return n;
}
function select(parent,name,label,options,value){
 const wrap=el('label',label),n=el('select');n.id='twsl-'+name;wrap.htmlFor=n.id;for(const [v,t]of options){const o=el('option',t);o.value=v;n.append(o);}if(value!==null)n.value=value;wrap.append(n);parent.append(wrap);fields[name]=n;return n;
}
function group(parent,label,open=false){const d=el('details');d.open=open;d.append(el('summary',label));parent.append(d);return d;}
function syncCountry(){const active=fields.region.value==='country';fields.country.disabled=!active;fields.country.parentElement.hidden=!active;}
async function saveFilters(){
 const min=Number(fields.min.value),max=Number(fields.max.value),dog=Number(fields.dog.value),country=fields.country.value.trim().toUpperCase();
 if(![min,max,dog].every(x=>Number.isFinite(x)&&x>1&&x<=1e6)||min>max){text(filterStatusBox,'Use multipliers greater than 1, with minimum no larger than maximum.');return;}
 if(fields.region.value==='country'&&!/^[A-Z]{2}$/.test(country)){text(filterStatusBox,'Enter a two-letter country code, such as GB or BR.');fields.country.focus();return;}
 cfg={...cfg,min,max,dog,country,sex:fields.sex.value,region:fields.region.value,sports:[...sportBox.selectedOptions].map(o=>o.value),events:[...eventBox.selectedOptions].map(o=>o.value)};
 const saved=await savePrefs();text(filterStatusBox,saved?'Filters saved.':'Filters applied for this session; saving failed.');log('Filters applied',{sports:cfg.sports.length,events:cfg.events.length,countryMode:cfg.region});render();
}
function mount(){
 if(root){if(!uiStyle.isConnected)document.documentElement.append(uiStyle);if(!root.isConnected)document.body.append(root);return;}
 uiStyle=el('style');uiStyle.id='twsl-ui-css';uiStyle.textContent=`
 #tw-shortlist{position:fixed;width:380px;max-width:calc(100vw - 16px);z-index:2147483638;background:#151c27;color:#e5eaf2;border:1px solid #53647d;border-radius:12px;box-shadow:0 8px 28px #0009;font:13px/1.45 Arial,sans-serif;box-sizing:border-box;overflow:hidden}
 #tw-shortlist *{box-sizing:border-box}#tw-shortlist .twsl-bar{display:flex;align-items:center;gap:6px;padding:6px 8px;background:#24334b;touch-action:none;cursor:move;user-select:none}
 #tw-shortlist .twsl-bar strong{flex:1}#tw-shortlist button,#tw-shortlist input,#tw-shortlist select{font:inherit;background:#26344a;color:#fff;border:1px solid #718199;border-radius:5px;padding:7px;min-height:40px;max-width:100%}
 #tw-shortlist button{cursor:pointer;touch-action:manipulation}#tw-shortlist button:disabled{opacity:.55;cursor:default}#tw-shortlist .twsl-body{padding:10px;max-height:62vh;max-height:62dvh;overflow:auto;overscroll-behavior:contain}
 #tw-shortlist p{margin:6px 0}#tw-shortlist article{padding:9px 0;border-bottom:1px solid #445268}#tw-shortlist .twsl-torn{color:#b7b7b7}#tw-shortlist .twsl-web{color:#a4d8f4}#tw-shortlist .twsl-coverage{color:#f0c67f;font-size:12px;margin:7px 0}
 #tw-shortlist a.twsl-match{display:block;color:#0047ab!important;background:#e4edff;padding:6px;border-radius:5px;font-weight:bold;text-decoration:underline;overflow-wrap:anywhere;margin-bottom:4px}
 #tw-shortlist label{display:block;margin:9px 0}#tw-shortlist label>input:not([type=checkbox]),#tw-shortlist label>select{display:block;width:100%;margin-top:4px}
 #tw-shortlist label.twsl-check{display:flex;align-items:center;gap:8px;min-height:40px}#tw-shortlist input[type=checkbox]{width:20px;height:20px;min-height:20px;margin:0;flex:none;accent-color:#458cff;order:-1}
 #tw-shortlist .twsl-actions{display:flex;flex-wrap:wrap;gap:6px;margin:5px 0}#tw-shortlist .twsl-numbers{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:7px}#tw-shortlist .twsl-numbers input{min-width:0}
 #tw-shortlist summary{cursor:pointer;min-height:40px;display:list-item;padding:8px 0;color:#c6dbf5}#tw-shortlist details{margin:5px 0}#tw-shortlist details>details{padding-left:8px}#tw-shortlist [role=status]{overflow-wrap:anywhere}#tw-shortlist [hidden]{display:none!important}
 #tw-shortlist[data-twsl-view=collapsed]{width:48px;height:48px;border-radius:50%}#tw-shortlist[data-twsl-view=collapsed]>.twsl-bar,#tw-shortlist[data-twsl-view=collapsed]>.twsl-body{display:none}
 #tw-shortlist-token{display:none;width:48px;height:48px;border:0!important;font-size:25px!important;touch-action:none}#tw-shortlist[data-twsl-view=collapsed]>#tw-shortlist-token{display:block}
 #tw-shortlist #tw-shortlist-support{position:static!important;inset:auto!important;width:100%!important;margin-top:12px}#tw-shortlist button:focus-visible,#tw-shortlist summary:focus-visible{outline:2px solid #a4d8f4}
 `;document.documentElement.append(uiStyle);
 root=el('section');root.id='tw-shortlist';root.setAttribute('aria-label','Bookie shortlist');
 const token=button('🎟️',()=>{cfg.collapsed=false;render();void savePrefs();});token.id='tw-shortlist-token';token.title='Open Bookie shortlist; drag to move';token.setAttribute('aria-label','Open Bookie shortlist');drag(token);
 const bar=el('div',undefined,'twsl-bar');gearButton=button('⚙️',()=>showSettings(settings.hidden));gearButton.id='twsl-settings-toggle';gearButton.title='Settings';gearButton.setAttribute('aria-label','Settings');gearButton.setAttribute('aria-expanded','false');
 const minimize=button('−',()=>{cfg.collapsed=true;render();void savePrefs();});minimize.setAttribute('aria-label','Minimize shortlist');bar.append(el('strong','🎟️ Bookie shortlist'),gearButton,minimize);drag(bar);
 body=el('div',undefined,'twsl-body');home=el('div');settings=el('section');settings.hidden=true;
 statusBox=el('div');statusBox.setAttribute('role','status');statusBox.hidden=true;
 const actions=el('div',undefined,'twsl-actions');externalButton=button('Check external odds',()=>void refreshExternal());externalButton.id='twsl-check-external';
 const recheck=button('Recheck',()=>{scanDOM();render();note('Captured data rechecked. Open or reopen matches to capture prices.');});recheck.title='Recheck loaded markets; this does not request new prices';
 stopButton=button('Stop',()=>{stopped=true;stopButton.disabled=true;providerStatus='Stopping after the current request...';render();});stopButton.id='twsl-stop';stopButton.hidden=true;bar.insertBefore(stopButton,gearButton);
 actions.append(externalButton,recheck);coverageBox=el('div',undefined,'twsl-coverage');resultBox=el('div');providerBox=el('p',undefined,'twsl-web');providerBox.setAttribute('role','status');
 home.append(statusBox,actions,coverageBox,resultBox,providerBox);
 const about=group(home,'Coverage and method');coverageDetails=el('p');about.append(coverageDetails,el('p','Next 24 hours, up to five matches. Rank uses normalized Torn implied probability, including draw odds. This is an estimate, not a measured win rate.'));
 settings.append(button('← Back to shortlist',()=>showSettings(false)),el('p','Version '+VERSION));
 externalSettings=group(settings,'External odds',true);
 const keyField=field(externalSettings,'key','The Odds API key (optional)','password',key);keyField.spellcheck=false;keyField.setAttribute('autocapitalize','none');
 keyField.addEventListener('input',()=>{keyStatus=keyField.value.trim()===key?(key?'Saved key loaded.':'No key saved.'):'Key edited. Tap Save & test key.';render();});
 rememberBox=field(externalSettings,'remember','Remember key on this device','checkbox','');rememberBox.checked=!!key;rememberBox.parentElement.className='twsl-check';
 select(externalSettings,'providerRegion','Bookmaker region',[['eu','Europe'],['uk','United Kingdom'],['us','US'],['au','Australia']],cfg.providerRegion);
 const keyActions=el('div',undefined,'twsl-actions');testButton=button('Save & test key',()=>void loadSports());testButton.id='twsl-test-key';
 const forgetButton=button('Forget key',async()=>{if(busy)return;key='';fields.key.value='';rememberBox.checked=false;cache.clear();external.clear();catalog=[];quota={};externalLoaded=false;scanComplete=false;keyStatus=await put('key','',true)?'Key removed.':'Key removed from session; storage could not be cleared.';providerStatus='External: not checked.';render();});
 keyActions.append(testButton,forgetButton);keyStatusBox=el('p',undefined,'twsl-web');keyStatusBox.setAttribute('role','status');providerSettingsBox=el('p',undefined,'twsl-web');externalSettings.append(keyActions,keyStatusBox,providerSettingsBox);
 const filters=group(settings,'Shortlist filters');const numbers=el('div',undefined,'twsl-numbers');filters.append(numbers);
 for(const [k,t]of [['min','Favorite min'],['max','Favorite max'],['dog','Opponent min']]){const n=field(numbers,k,t,'number',cfg[k]);n.step='0.01';n.min='1.01';n.inputMode='decimal';}
 select(filters,'sex','Event category',[['both','Both, including unknown'],['men','Men only, explicitly identified'],['women','Women only, explicitly identified']],cfg.sex);
 select(filters,'region','Event country (not team nationality)',[['all','All countries, including unknown'],['us','United States'],['country','Specific country'],['international','Outside US, known countries only']],cfg.region).addEventListener('change',syncCountry);
 field(filters,'country','Two-letter country code, e.g. GB, BR','text',cfg.country).maxLength=2;syncCountry();
 const selections=group(filters,'Choose sports or matches');sportBox=select(selections,'sports','Sports: none selected means all',[],null);sportBox.multiple=true;sportBox.size=4;
 eventBox=select(selections,'events','Matches: none selected means all',[],null);eventBox.multiple=true;eventBox.size=4;
 selections.append(button('Use all sports and matches',()=>{for(const box of [sportBox,eventBox])for(const o of box.options)o.selected=false;}));
 filterStatusBox=el('p');filterStatusBox.setAttribute('role','status');const saveButton=button('Save filters',()=>void saveFilters());saveButton.id='twsl-save-filters';filters.append(saveButton,filterStatusBox);
 const diagnostics=group(settings,'Diagnostics and support'),debugActions=el('div',undefined,'twsl-actions');debugActions.append(button('🪲',()=>MyDebug.toggleView()),button('📋 Copy Logs to Clipboard',function(){void MyDebug.copy(this);}));diagnostics.append(debugActions);
 const host=el('div');host.id='tw-shortlist-support-host';diagnostics.append(host);
 const privacy=group(settings,'Storage and privacy');privacy.append(el('p','No Torn key is needed. The external key goes only to The Odds API. Remember stores it in userscript storage, if available. Preferences can use localStorage. No bets are placed or betting history sent. Uncheck Remember and Save & test to remove a stored key while using it this session.'));
 body.append(home,settings);root.append(token,bar,body);document.body.append(root);
 support=new SupportModule({containerId:'tw-shortlist-support',styleId:'tw-shortlist-support-css',getParent:()=>host});clamp();
}
function relevantMutation(m){
 const n=m.target.nodeType===1?m.target:m.target.parentElement;
 if(n?.closest('#tw-shortlist,[id^="tw-debug-"],[id^="twsl-"]'))return false;
 if(n?.closest('.matchName,ul.bets-wrap,li.c-pointer,li.disabled'))return true;
 return [...m.addedNodes,...m.removedNodes].some(x=>x.nodeType===1&&(x.matches('.matchName,ul.bets-wrap,li.c-pointer')||x.querySelector('.matchName,ul.bets-wrap')));
}
hook();
async function boot(){
 const stored=await get('settings',{});cfg={...defaults,...(stored&&typeof stored==='object'?stored:{})};
 if(!Array.isArray(cfg.sports))cfg.sports=[];if(!Array.isArray(cfg.events))cfg.events=[];
 if(![cfg.min,cfg.max,cfg.dog].every(x=>Number.isFinite(x)&&x>1&&x<=1e6)||cfg.min>cfg.max)Object.assign(cfg,{min:1.3,max:2.5,dog:4});
 if(!['both','men','women'].includes(cfg.sex))cfg.sex='both';if(!['all','us','country','international'].includes(cfg.region))cfg.region='all';
 if(!['eu','us','uk','au'].includes(cfg.providerRegion))cfg.providerRegion='eu';cfg.country=String(cfg.country||'').toUpperCase();
 key=await get('key','',true);if(typeof key!=='string')key='';key=key.trim();keyStatus=key?'Saved key loaded; tap Save & test key to verify it.':'No key saved.';
 mount();scanDOM();render();
 const observer=new MutationObserver(ms=>{if(!root.isConnected||!uiStyle.isConnected||ms.some(relevantMutation))schedule();});
 observer.observe(document.documentElement,{childList:true,subtree:true,characterData:true,attributes:true,attributeFilter:['disabled','aria-disabled','class','title','data-start-timestamp','data-start-time','data-start','datetime','href']});
 window.addEventListener('hashchange',schedule);window.addEventListener('resize',clamp);window.visualViewport?.addEventListener('resize',clamp);document.addEventListener('visibilitychange',()=>{if(!document.hidden)schedule();});
 // Expiry-only timer. DOM discovery and requests are never polled.
 window.setInterval(()=>{if(!document.hidden)render();},30000);
 log('Ready',{version:VERSION,mode:'partial-coverage',keyPresent:!!key});
}
if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',()=>void boot(),{once:true});else void boot();

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
