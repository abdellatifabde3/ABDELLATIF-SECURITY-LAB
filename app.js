'use strict';
const $ = id => document.getElementById(id);
const reports = [];
const LIMITS = { file: 512 * 1024 * 1024, dex: 64 * 1024 * 1024, totalDex: 160 * 1024 * 1024, entryBytes: 256 * 1024 * 1024, totalExpanded: 1024 * 1024 * 1024, entries: 20000, batch: 20, sessionReports: 50 };
const PERMISSION_TOKENS = ['INTERNET','READ_SMS','RECEIVE_SMS','SEND_SMS','READ_CONTACTS','WRITE_CONTACTS','ACCESS_FINE_LOCATION','ACCESS_COARSE_LOCATION','CAMERA','RECORD_AUDIO','READ_CALL_LOG','WRITE_CALL_LOG','READ_PHONE_STATE','REQUEST_INSTALL_PACKAGES','SYSTEM_ALERT_WINDOW','BIND_ACCESSIBILITY_SERVICE'];
const INDICATOR_TOKENS = ['http://','https://','DexClassLoader','PathClassLoader','Runtime.getRuntime','/system/bin/su','getDeviceId','loadLibrary','AccessibilityService','SmsManager','ProcessBuilder','su -c','RECEIVE_BOOT_COMPLETED','DeviceAdminReceiver'];
function fmt(n){return n<1024?`${n} B`:n<1048576?`${(n/1024).toFixed(1)} KB`:`${(n/1048576).toFixed(2)} MB`;}
function esc(s){return String(s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));}
async function sha(buf){const h=await crypto.subtle.digest('SHA-256',buf);return [...new Uint8Array(h)].map(x=>x.toString(16).padStart(2,'0')).join('');}
function u16(v,p){if(p<0||p+2>v.byteLength)throw Error('بنية ZIP غير مكتملة');return v.getUint16(p,true);}
function u32(v,p){if(p<0||p+4>v.byteLength)throw Error('بنية ZIP غير مكتملة');return v.getUint32(p,true);}
const CRC32_TABLE=(()=>{const t=new Uint32Array(256);for(let n=0;n<256;n++){let c=n;for(let k=0;k<8;k++)c=(c&1)?(0xedb88320^(c>>>1)):(c>>>1);t[n]=c>>>0;}return t;})();
function crc32(bytes){let c=0xffffffff;for(const b of bytes)c=CRC32_TABLE[(c^b)&255]^(c>>>8);return (c^0xffffffff)>>>0;}
function auditArchive(entries){
 const names=entries.map(e=>e.name),seen=new Set(),duplicates=[],unsafePaths=[],highRatios=[],unsupported=[],overlaps=[];let totalUncompressed=0;
 for(const e of entries){
  const normalized=e.name.replace(/\\/g,'/');
  if(seen.has(normalized))duplicates.push(e.name);seen.add(normalized);
  if(normalized.startsWith('/')||/^[a-z]:/i.test(normalized)||normalized.split('/').some(part=>part==='..'))unsafePaths.push(e.name);
  totalUncompressed+=e.uncompressedSize;
  if(e.compressedSize===0?e.uncompressedSize>0:e.uncompressedSize/e.compressedSize>100)highRatios.push(e.name);
  if(![0,8].includes(e.method))unsupported.push(e.name);
 }
 const byOffset=[...entries].sort((a,b)=>a.localOffset-b.localOffset);for(let i=1;i<byOffset.length;i++){const prev=byOffset[i-1],cur=byOffset[i],prevEnd=prev.dataStart+prev.compressedSize;if(cur.localOffset<prevEnd)overlaps.push(`${prev.name} ↔ ${cur.name}`);}
 return {duplicateNames:[...new Set(duplicates)],unsafePaths,highCompressionRatio:highRatios,unsupportedCompression:unsupported,overlappingEntries:overlaps,totalUncompressedBytes:totalUncompressed,entryCount:entries.length,structurallyReviewable:!duplicates.length&&!unsafePaths.length&&!highRatios.length&&!overlaps.length&&totalUncompressed<=LIMITS.totalExpanded};
}
function parseZip(buf){
 const v=new DataView(buf),bytes=new Uint8Array(buf);let end=-1;
 for(let p=bytes.length-22;p>=Math.max(0,bytes.length-65557);p--){if(u32(v,p)===0x06054b50){end=p;break;}}
 if(end<0)throw Error('الملف ليس أرشيف ZIP/APK صالحاً أو أن بنية ZIP64 غير مدعومة.');
 if(u16(v,end+4)!==0||u16(v,end+6)!==0)throw Error('الأرشيف متعدد الأقراص غير مدعوم.');
 const commentLength=u16(v,end+20);
 if(end+22+commentLength!==buf.byteLength)throw Error('طول تعليق ZIP لا يطابق نهاية الملف؛ قد يكون سجل النهاية ملتبساً.');
 const count=u16(v,end+10),cdSize=u32(v,end+12),cdStart=u32(v,end+16);
 if(count===0xffff||cdSize===0xffffffff||cdStart===0xffffffff)throw Error('أرشيف ZIP64 غير مدعوم حالياً.');
 if(count>LIMITS.entries)throw Error(`عدد عناصر ZIP يتجاوز الحد الآمن (${LIMITS.entries.toLocaleString('ar')}).`);
 if(cdStart+cdSize>end||cdStart+cdSize>buf.byteLength)throw Error('جدول ملفات ZIP غير صالح أو يتجاوز الحدود.');
 let p=cdStart;const entries=[];
 for(let i=0;i<count;i++){
  if(u32(v,p)!==0x02014b50)throw Error('تعذر قراءة سجل ملف داخل ZIP.');
  const flags=u16(v,p+8),method=u16(v,p+10),crc=u32(v,p+16),compressedSize=u32(v,p+20),uncompressedSize=u32(v,p+24),nl=u16(v,p+28),el=u16(v,p+30),cl=u16(v,p+32),localOffset=u32(v,p+42);
  if(flags&1)throw Error('الأرشيف يحتوي ملفات مشفرة بكلمة مرور ولا يمكن فحصها.');
  if(compressedSize===0xffffffff||uncompressedSize===0xffffffff||localOffset===0xffffffff)throw Error('مدخل ZIP64 غير مدعوم.');
  if(p+46+nl+el+cl>cdStart+cdSize)throw Error('اسم أو بيانات وصف ملف ZIP غير مكتملة.');
  const name=new TextDecoder().decode(bytes.slice(p+46,p+46+nl));
  if(localOffset>=cdStart||localOffset+30>cdStart||localOffset+30>buf.byteLength)throw Error('إزاحة ملف محلي تقع خارج منطقة بيانات ZIP.');
  if(u32(v,localOffset)!==0x04034b50)throw Error('إزاحة ملف محلي غير صالحة.');
  const localFlags=u16(v,localOffset+6),localMethod=u16(v,localOffset+8),localName=u16(v,localOffset+26),localExtra=u16(v,localOffset+28);
  if(localFlags!==flags||localMethod!==method)throw Error('عدم تطابق ترويسة ZIP المحلية والمركزية.');
  const dataStart=localOffset+30+localName+localExtra;
  if(dataStart>cdStart||dataStart>buf.byteLength||localOffset+30+localName>cdStart)throw Error('ترويسة ملف ZIP المحلية تتجاوز بداية الجدول المركزي.');
  const localFileName=new TextDecoder().decode(bytes.slice(localOffset+30,localOffset+30+localName));
  if(localFileName!==name)throw Error('اسم الملف في ترويسة ZIP المحلية لا يطابق الجدول المركزي.');
  if(dataStart+compressedSize>cdStart)throw Error('بيانات ملف مضغوط تتداخل مع الجدول المركزي أو كتلة توقيع APK.');
  if(uncompressedSize>LIMITS.entryBytes)throw Error(`العنصر ${name} يتجاوز حد الحجم المفكوك الآمن (${fmt(LIMITS.entryBytes)}).`);
  entries.push({name,flags,method,crc,compressedSize,uncompressedSize,dataStart,localOffset});
  p+=46+nl+el+cl;
 }
 if(p!==cdStart+cdSize)throw Error('حجم جدول ZIP المركزي لا يطابق السجلات المقروءة.');
 const localOrder=[...entries].sort((a,b)=>a.localOffset-b.localOffset);
 for(let i=1;i<localOrder.length;i++){const prev=localOrder[i-1],cur=localOrder[i];if(cur.localOffset<prev.dataStart+prev.compressedSize)throw Error(`تداخل سجلات ZIP المحلية: ${prev.name} و ${cur.name}.`);}
 const expanded=entries.reduce((sum,e)=>sum+e.uncompressedSize,0);
 if(expanded>LIMITS.totalExpanded)throw Error(`الحجم الإجمالي بعد فك الضغط يتجاوز الحد الآمن (${fmt(LIMITS.totalExpanded)}).`);
 return entries;
}
async function extractEntry(entry,buf,maxBytes){
 if(entry.uncompressedSize>maxBytes)throw Error(`الملف الداخلي ${entry.name} يتجاوز حد القراءة الآمن.`);
 const data=buf.slice(entry.dataStart,entry.dataStart+entry.compressedSize);
 if(entry.method===0){if(data.byteLength!==entry.uncompressedSize)throw Error('حجم الملف المخزن غير متطابق.');const out=new Uint8Array(data);if(crc32(out)!==entry.crc)throw Error(`فشل التحقق من CRC32 للملف ${entry.name}.`);return out;}
 if(entry.method!==8)throw Error(`طريقة الضغط ${entry.method} غير مدعومة للملف ${entry.name}.`);
 if(!('DecompressionStream'in window))throw Error('المتصفح لا يدعم فك ضغط Deflate المطلوب للتحليل.');
 const stream=new Blob([data]).stream().pipeThrough(new DecompressionStream('deflate-raw'));
 const reader=stream.getReader(),chunks=[];let total=0;
 try{while(true){const {done,value}=await reader.read();if(done)break;total+=value.byteLength;if(total>maxBytes){await reader.cancel();throw Error('تجاوز فك الضغط الحد الآمن للذاكرة.');}chunks.push(value);}}finally{reader.releaseLock();}
 if(total!==entry.uncompressedSize)throw Error(`حجم الملف بعد فك الضغط غير متطابق: ${entry.name}`);
 const out=new Uint8Array(total);let at=0;for(const c of chunks){out.set(c,at);at+=c.length;}if(crc32(out)!==entry.crc)throw Error(`فشل التحقق من CRC32 للملف ${entry.name}.`);return out;
}
function readLength8(a,p){let n=a[p++];if(n&0x80)n=((n&0x7f)<<8)|a[p++];return [n,p];}
function readLength16(v,p){let n=v.getUint16(p,true);if(n&0x8000)n=((n&0x7fff)<<16)|v.getUint16(p+2,true),p+=2;return [n,p+2];}
function parseStringPool(bytes,v,base,size){
 const count=u32(v,base+8),flags=u32(v,base+16),stringsStart=u32(v,base+20),utf8=!!(flags&0x100);
 if(count>200000||stringsStart>=size)throw Error('String pool غير صالح.');
 const out=[];for(let i=0;i<count;i++){
  const off=u32(v,base+28+i*4),p=base+stringsStart+off;if(p<base||p>=base+size)throw Error('إزاحة نص Manifest غير صالحة.');
  if(utf8){let q=p;[,q]=readLength8(bytes,q);let [len,end]=readLength8(bytes,q);if(end+len>=base+size)throw Error('نص UTF-8 يتجاوز حدود String pool.');out.push(new TextDecoder('utf-8').decode(bytes.slice(end,end+len)));}
  else{let [len,end]=readLength16(v,p);if(end+len*2>base+size)throw Error('نص UTF-16 يتجاوز حدود String pool.');let units=[];for(let j=0;j<len;j++)units.push(v.getUint16(end+j*2,true));out.push(String.fromCharCode(...units));}
 }
 return out;
}
function parseBinaryManifest(bytes){
 const v=new DataView(bytes.buffer,bytes.byteOffset,bytes.byteLength);if(bytes.length<8||u16(v,0)!==0x0003)throw Error('AndroidManifest.xml ليس Binary XML صالحاً.');
 const total=u32(v,4);if(total>bytes.length||total<8)throw Error('حجم Binary XML غير صالح.');
 let p=8,strings=[],resourceIds=[],app={packageName:'',versionName:'',versionCode:'',minSdk:'',targetSdk:'',permissions:[],components:[],application:{},usesFeatures:[]};
 const str=i=>i===0xffffffff||i<0||i>=strings.length?'':strings[i];
 while(p+8<=total){const type=u16(v,p),header=u16(v,p+2),size=u32(v,p+4);if(size<8||p+size>total)throw Error('Chunk في Manifest غير صالح.');
  if(type===0x0001)strings=parseStringPool(bytes,v,p,size);
  else if(type===0x0180){const count=Math.floor((size-header)/4);for(let i=0;i<count;i++)resourceIds.push(u32(v,p+header+i*4));}
  else if(type===0x0102){
   if(header<16||size<36)throw Error('عنصر XML غير مكتمل.');const ns=u32(v,p+16),nameIndex=u32(v,p+20),tag=str(nameIndex),attrStart=u16(v,p+24),attrSize=u16(v,p+26),attrCount=u16(v,p+28);if(attrSize<20||attrCount>1000)throw Error('جدول خصائص Manifest غير صالح.');
   const attrs={},start=p+16+attrStart;
   for(let i=0;i<attrCount;i++){const q=start+i*attrSize;if(q+20>p+size)throw Error('خاصية Manifest تتجاوز حدود العنصر.');const key=str(u32(v,q+4)),raw=u32(v,q+8),valType=bytes[q+15],data=u32(v,q+16);let value=raw===0xffffffff?'':str(raw);if(value===''&&valType===3)value=str(data);else if(value===''&&valType===18)value=data!==0?'true':'false';else if(value===''&&valType===16)value=String(data);else if(value===''&&valType===17)value='0x'+data.toString(16);attrs[key]=value;}
   if(tag==='manifest'){app.packageName=attrs.package||'';app.versionName=attrs.versionName||'';app.versionCode=attrs.versionCode||attrs.versionCodeMajor||'';}
   else if(tag==='uses-sdk'){app.minSdk=attrs.minSdkVersion||'';app.targetSdk=attrs.targetSdkVersion||'';}
   else if(tag==='uses-permission'||tag==='uses-permission-sdk-23'||tag==='uses-permission-sdk-m')app.permissions.push(attrs.name||'');
   else if(tag==='uses-feature')app.usesFeatures.push({name:attrs.name||'',required:attrs.required||'true'});
   else if(tag==='application')app.application={label:attrs.label||'',debuggable:attrs.debuggable||'false',allowBackup:attrs.allowBackup||'true',usesCleartextTraffic:attrs.usesCleartextTraffic||'false',networkSecurityConfig:attrs.networkSecurityConfig||''};
   else if(['activity','activity-alias','service','receiver','provider'].includes(tag))app.components.push({type:tag,name:attrs.name||'',exported:attrs.exported||'unspecified',permission:attrs.permission||'',enabled:attrs.enabled||'true'});
  }
  p+=size;
 }
 app.permissions=[...new Set(app.permissions.filter(Boolean))];return app;
}
function detectApkSignatures(buf,entries){
 const v=new DataView(buf),bytes=new Uint8Array(buf);let eocd=-1;
 for(let p=bytes.length-22;p>=Math.max(0,bytes.length-65557);p--){if(u32(v,p)===0x06054b50){eocd=p;break;}}
 const v1Files=entries.filter(e=>/^META-INF\/[^/]+\.(RSA|DSA|EC|SF)$/i.test(e.name)).map(e=>e.name);
 let v2v3=false,v2v3BlockSize=null;
 if(eocd>=0){const cdOffset=u32(v,eocd+16);if(cdOffset>=24&&cdOffset<=bytes.length){const magic='APK Sig Block 42';let found=true;for(let i=0;i<16;i++)if(bytes[cdOffset-16+i]!==magic.charCodeAt(i)){found=false;break;}if(found){v2v3=true;const low=BigInt(u32(v,cdOffset-24)),high=BigInt(u32(v,cdOffset-20));v2v3BlockSize=Number((high<<32n)|low)+8;}}}
 const hasV1Cert=v1Files.some(n=>/\.(RSA|DSA|EC)$/i.test(n));
 return {schemes:{v1:hasV1Cert,v2v3BlockPresent:v2v3},v1Files,v2v3BlockSize,verification:'تم التعرف على مؤشرات بنية التوقيع فقط؛ لم يتم التحقق تشفيرياً من سلسلة الشهادة أو التوقيع أو صلاحية الثقة.',limitations:['قد تستخدم APK توقيعات v2/v3/v4 أو أكثر من مخطط.','وجود ملفات META-INF أو Signing Block لا يثبت أن التوقيع صالح.','تم استخراج حقول X.509 وبصمة الشهادة عند توفر بنية DER قابلة للقراءة؛ لم يتم التحقق من سلسلة الثقة أو التوقيع التشفيري.']};
}
function derRead(bytes,offset){
 if(offset<0||offset+2>bytes.length)throw Error('DER header خارج الحدود.');
 const tag=bytes[offset++];let length=bytes[offset++];
 if(length&0x80){const count=length&0x7f;if(!count||count>4||offset+count>bytes.length)throw Error('طول DER غير صالح.');length=0;for(let i=0;i<count;i++)length=length*256+bytes[offset++];}
 const start=offset,end=start+length;if(end>bytes.length)throw Error('قيمة DER تتجاوز حدود الملف.');
 return {tag,start,end,next:end,length};
}
function derChildren(bytes,node){const out=[];let p=node.start;while(p<node.end){const child=derRead(bytes,p);out.push(child);p=child.next;}if(p!==node.end)throw Error('بنية DER غير متطابقة.');return out;}
function derOid(bytes,node){if(node.tag!==0x06||node.length<1)return '';const a=bytes.slice(node.start,node.end),parts=[];parts.push(Math.min(2,Math.floor(a[0]/40)),a[0]-(Math.min(2,Math.floor(a[0]/40))*40));let value=0;for(let i=1;i<a.length;i++){value=(value<<7)|(a[i]&127);if(!(a[i]&128)){parts.push(value);value=0;}}return parts.join('.');}
const X509_OIDS={'2.5.4.3':'CN','2.5.4.6':'C','2.5.4.7':'L','2.5.4.8':'ST','2.5.4.10':'O','2.5.4.11':'OU','1.2.840.113549.1.9.1':'emailAddress'};
function derText(bytes,node){const raw=bytes.slice(node.start,node.end);if(node.tag===0x0c)return new TextDecoder('utf-8').decode(raw);if(node.tag===0x1e){let out='';for(let i=0;i+1<raw.length;i+=2)out+=String.fromCharCode((raw[i]<<8)|raw[i+1]);return out;}return new TextDecoder('latin1').decode(raw);}
function x509Name(bytes,node){try{return derChildren(bytes,node).map(set=>derChildren(bytes,set).map(pair=>{const a=derChildren(bytes,pair);return a.length>=2?`${X509_OIDS[derOid(bytes,a[0])]||derOid(bytes,a[0])}=${derText(bytes,a[1])}`:'';}).filter(Boolean).join('+')).filter(Boolean).join(', ');}catch{return 'غير قابل للقراءة';}}
function derTime(bytes,node){const raw=derText(bytes,node);let d;if(node.tag===0x17){const m=raw.match(/^(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})?Z$/);if(!m)return raw;const y=Number(m[1])+(Number(m[1])>=50?1900:2000);d=new Date(Date.UTC(y,+m[2]-1,+m[3],+m[4],+m[5],+(m[6]||0)));}else if(node.tag===0x18){const m=raw.match(/^(\d{4})(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})Z$/);if(!m)return raw;d=new Date(Date.UTC(+m[1],+m[2]-1,+m[3],+m[4],+m[5],+m[6]));}else return raw;return Number.isNaN(d?.getTime())?raw:d.toISOString();}
function certificateCandidate(bytes,node){
 if(node.tag!==0x30)return null;let c;try{c=derChildren(bytes,node);}catch{return null;}
 if(c.length<3||c[0].tag!==0x30||c[1].tag!==0x30||c[2].tag!==0x03)return null;
 let t;try{t=derChildren(bytes,c[0]);}catch{return null;}let i=0;if(t[0]?.tag===0xa0)i++;
 if(t.length<i+6||t[i]?.tag!==0x02||t[i+1]?.tag!==0x30||t[i+2]?.tag!==0x30||t[i+3]?.tag!==0x30||t[i+4]?.tag!==0x30||t[i+5]?.tag!==0x30)return null;
 const sigAlg=(()=>{try{const x=derChildren(bytes,c[1]);return x[0]?derOid(bytes,x[0]):'';}catch{return '';}})();
 const serial=[...bytes.slice(t[i].start,t[i].end)].map(x=>x.toString(16).padStart(2,'0')).join('').replace(/^00(?=..)/,'');
 return {serial,signatureOid:sigAlg,issuer:x509Name(bytes,t[i+2]),notBefore:derTime(bytes,derChildren(bytes,t[i+3])[0]),notAfter:derTime(bytes,derChildren(bytes,t[i+3])[1]),subject:x509Name(bytes,t[i+4]),spkiPresent:t[i+5].tag===0x30,derStart:node.start,derEnd:node.end};
}
async function inspectX509Certificates(bytes,sourceName){
 const found=[],seen=new Set(),maxNodes=20000;let visited=0;
 function walk(node,depth){if(depth>20||visited++>maxNodes)return;const cert=certificateCandidate(bytes,node);if(cert){const key=`${cert.derStart}:${cert.derEnd}`;if(!seen.has(key)){seen.add(key);found.push(cert);}return;}if((node.tag&0x20)===0)return;let children;try{children=derChildren(bytes,node);}catch{return;}for(const child of children)walk(child,depth+1);}
 try{let p=0;while(p<bytes.length){const n=derRead(bytes,p);walk(n,0);p=n.next;}}catch{}
 const out=[];for(const cert of found){const der=bytes.slice(cert.derStart,cert.derEnd);cert.sha256=await sha(der.buffer.slice(der.byteOffset,der.byteOffset+der.byteLength));cert.source=sourceName;const expiry=Date.parse(cert.notAfter),start=Date.parse(cert.notBefore),now=Date.now();cert.validity=Number.isFinite(expiry)&&Number.isFinite(start)?(now<start?'not-yet-valid':now>expiry?'expired':'currently-valid'):'unknown';delete cert.derStart;delete cert.derEnd;out.push(cert);}
 return out;
}
const SETTINGS_KEY='asl.lab.preferences';
const DEFAULT_SETTINGS={compactMode:false,confirmHistoryClear:true};
function settingsLoad(){
 try{const value=JSON.parse(localStorage.getItem(SETTINGS_KEY)||'{}');return {compactMode:value?.compactMode===true,confirmHistoryClear:value?.confirmHistoryClear!==false};}
 catch{return {...DEFAULT_SETTINGS};}
}
function settingsApply(settings=settingsLoad()){
 document.body?.classList?.toggle('compact-mode',settings.compactMode);
 const compact=$('compactMode'),confirmClear=$('confirmHistoryClear');
 if(compact)compact.checked=settings.compactMode;
 if(confirmClear)confirmClear.checked=settings.confirmHistoryClear;
}
function settingsSave(){
 const settings={compactMode:$('compactMode')?.checked===true,confirmHistoryClear:$('confirmHistoryClear')?.checked!==false};
 try{localStorage.setItem(SETTINGS_KEY,JSON.stringify(settings));settingsApply(settings);$('status').textContent='تم حفظ إعدادات المختبر على هذا الجهاز.';}
 catch{$('status').textContent='تعذر حفظ الإعدادات؛ قد تكون مساحة التخزين ممتلئة أو معطلة.';}
}
function historyDelete(hash){
 const items=historyLoad(),next=items.filter(item=>item.hash!==hash);
 if(next.length===items.length)return false;
 localStorage.setItem('asl.analysis.history',JSON.stringify(next));historyRender();return true;
}
function historyLoad(){
 try{const value=JSON.parse(localStorage.getItem('asl.analysis.history')||'[]');return Array.isArray(value)?value.filter(x=>x&&typeof x==='object'&&typeof x.hash==='string').slice(0,100):[];}
 catch{return [];}
}
function historySave(report){
 try{const old=historyLoad(),item={name:String(report.name||'').slice(0,240),size:Number(report.size)||0,hash:String(report.hash||''),packageName:String(report.manifestData?.packageName||'').slice(0,240),version:String(report.manifestData?.versionName||'').slice(0,120),riskScore:Number(report.riskScore)||0,riskLevel:String(report.riskLevel||'غير محدد').slice(0,40),analyzedAt:new Date().toISOString()};const merged=[item,...old.filter(x=>x.hash!==item.hash)].slice(0,100);localStorage.setItem('asl.analysis.history',JSON.stringify(merged));historyRender();}
 catch{$('status').textContent='تعذر حفظ سجل التحليل؛ قد تكون مساحة التخزين ممتلئة أو معطلة.';}
}
function validateHistoryBackup(value){
 if(!value||typeof value!=='object'||value.schema!=='asl-history-backup'||![1,2].includes(value.version)||!Array.isArray(value.items))throw Error('صيغة النسخة الاحتياطية غير مدعومة.');
 if(value.version===2&&(!/^[a-f0-9]{64}$/i.test(String(value.checksum||''))))throw Error('بصمة سلامة النسخة الاحتياطية غير صالحة.');
 if(value.items.length>100)throw Error('تحتوي النسخة على أكثر من 100 سجل.');
 return value.items.map((x,i)=>{if(!x||typeof x!=='object'||typeof x.hash!=='string'||!/^[a-f0-9]{64}$/i.test(x.hash))throw Error(`بصمة غير صالحة في السجل رقم ${i+1}.`);const size=Number(x.size),risk=Number(x.riskScore);if(!Number.isFinite(size)||size<0||!Number.isFinite(risk)||risk<0||risk>100)throw Error(`بيانات رقمية غير صالحة في السجل رقم ${i+1}.`);const date=typeof x.analyzedAt==='string'&&Number.isFinite(Date.parse(x.analyzedAt))?new Date(x.analyzedAt).toISOString():new Date().toISOString();return {name:String(x.name||'ملف بلا اسم').slice(0,240),size,hash:x.hash.toLowerCase(),packageName:String(x.packageName||'').slice(0,240),version:String(x.version||'').slice(0,120),riskScore:risk,riskLevel:String(x.riskLevel||'غير محدد').slice(0,40),analyzedAt:date};});
}
async function createHistoryBackup(items=historyLoad()){
 const payload={tool:'ABDELLATIF SECURITY LAB',schema:'asl-history-backup',version:2,exportedAt:new Date().toISOString(),items};
 payload.checksum=await sha(new TextEncoder().encode(JSON.stringify(items)).buffer);
 return payload;
}
async function importHistoryBackup(file){
 if(!file) return; if(file.size>1024*1024)throw Error('حجم النسخة الاحتياطية يتجاوز 1 MB.');
 const parsed=JSON.parse(await file.text());
 if(parsed?.version===2){const actual=await sha(new TextEncoder().encode(JSON.stringify(parsed.items)).buffer);if(actual!==String(parsed.checksum||'').toLowerCase())throw Error('فشل التحقق من سلامة النسخة الاحتياطية؛ قد تكون البيانات تغيرت أو تلفت.');}
 const incoming=validateHistoryBackup(parsed),current=historyLoad(),seen=new Set(),merged=[];
 for(const item of [...incoming,...current])if(!seen.has(item.hash)){seen.add(item.hash);merged.push(item);if(merged.length===100)break;}
 localStorage.setItem('asl.analysis.history',JSON.stringify(merged));historyRender();return {imported:incoming.length,total:merged.length};
}
function historyRender(){
 const el=$('history');if(!el)return;const items=historyLoad(),query=($('historySearch')?.value||'').trim().toLocaleLowerCase('ar');
 const filtered=items.filter(x=>[x.name,x.packageName,x.version,x.hash].some(v=>String(v||'').toLocaleLowerCase('ar').includes(query)));
 el.innerHTML=filtered.length?filtered.map(x=>`<div class="history-row"><div><b>${esc(x.name||'ملف بلا اسم')}</b><small>${esc(x.packageName||'حزمة غير معروفة')} · ${esc(x.version||'—')} · ${Number.isFinite(Date.parse(x.analyzedAt))?new Date(x.analyzedAt).toLocaleString('ar'):'تاريخ غير معروف'}</small><code>${esc(x.hash)}</code></div><div class="history-row-meta"><span class="history-risk">${Number(x.riskScore)||0}/100 · ${esc(x.riskLevel||'غير محدد')}</span><button type="button" class="danger history-delete" data-delete-history="${esc(x.hash)}" aria-label="حذف سجل ${esc(x.name||'APK')}">حذف السجل</button></div></div>`).join(''):items.length?'<p class="muted">لا توجد نتائج مطابقة لبحثك.</p>':'<p class="muted">لا يوجد سجل محفوظ على هذا الجهاز.</p>';
 const optionMarkup=(label)=>`<option value="">${label}</option>`+items.map(x=>`<option value="${esc(x.hash)}">${esc(x.name||'ملف بلا اسم')} · ${esc(x.version||'—')} · ${esc(x.hash.slice(0,12))}</option>`).join('');
 const base=$('historyBase'),target=$('historyTarget');
 if(base){const selected=base.value;base.innerHTML=optionMarkup('الإصدار الأساسي');if(items.some(x=>x.hash===selected))base.value=selected;else if(items[0])base.value=items[0].hash;}
 if(target){const selected=target.value;target.innerHTML=optionMarkup('الإصدار المقارن');if(items.some(x=>x.hash===selected))target.value=selected;else if(items[1])target.value=items[1].hash;}
 const compareButton=$('compareHistory');if(compareButton)compareButton.disabled=items.length<2||!base?.value||!target?.value||base.value===target.value;
 const exportButton=$('exportHistory');if(exportButton)exportButton.disabled=!items.length;const backupButton=$('backupHistory');if(backupButton)backupButton.disabled=!items.length;
}
function compareHistoryRecords(base,target){
 if(!base||!target)throw Error('اختر سجلين للمقارنة.');
 if(base.hash===target.hash)throw Error('لا يمكن مقارنة الملف نفسه بنفسه.');
 const riskDelta=Number(target.riskScore)-Number(base.riskScore),sizeDelta=Number(target.size)-Number(base.size);
 const samePackage=!!base.packageName&&base.packageName===target.packageName;
 const baseTime=Date.parse(base.analyzedAt),targetTime=Date.parse(target.analyzedAt);
 return {tool:'ABDELLATIF SECURITY LAB',schemaVersion:'1.0',generatedAt:new Date().toISOString(),comparisonType:'history-metadata-only',baseline:{name:base.name,sha256:base.hash,packageName:base.packageName,version:base.version,size:base.size,riskScore:base.riskScore,riskLevel:base.riskLevel,analyzedAt:base.analyzedAt},target:{name:target.name,sha256:target.hash,packageName:target.packageName,version:target.version,size:target.size,riskScore:target.riskScore,riskLevel:target.riskLevel,analyzedAt:target.analyzedAt},identity:{samePackage,packageChanged:base.packageName!==target.packageName,identicalSha256:base.hash===target.hash,versionChanged:base.version!==target.version},changes:{riskDelta,riskDirection:riskDelta>0?'increased':riskDelta<0?'decreased':'unchanged',sizeDelta,analyzedLater:Number.isFinite(baseTime)&&Number.isFinite(targetTime)?targetTime>=baseTime:null},limitations:['هذه مقارنة لبيانات سجل مختصرة فقط.','لا تتضمن النسخة الاحتياطية الصلاحيات أو المكونات أو نتائج DEX.','لا يمكن استنتاج التغييرات البرمجية أو الحكم على سلامة التطبيق من هذه البيانات وحدها.']};
}
function renderHistoryComparison(c){
 const delta=(n)=>`${n>0?'+':''}${n}`;
 return `<article class="card history-comparison"><h3>مقارنة سجلات التحليل</h3><div class="grid"><div class="item"><small>الحزمة نفسها</small><b>${c.identity.samePackage?'نعم':'لا / غير متاح'}</b></div><div class="item"><small>تغير الإصدار</small><b>${c.identity.versionChanged?'نعم':'لا'}</b></div><div class="item"><small>تغير مؤشر المراجعة</small><b>${esc(delta(c.changes.riskDelta))} نقطة</b></div><div class="item"><small>تغير الحجم</small><b>${esc(delta(c.changes.sizeDelta))} بايت</b></div><div class="item"><small>تطابق SHA-256</small><b>${c.identity.identicalSha256?'نعم':'لا'}</b></div></div><p><b>الأساسي:</b> ${esc(c.baseline.name)} · ${esc(c.baseline.version||'—')}</p><p><b>المقارن:</b> ${esc(c.target.name)} · ${esc(c.target.version||'—')}</p><small>مقارنة وصفية لسجلات مختصرة فقط؛ لا تتوفر بيانات الصلاحيات أو المكونات أو DEX في سجل التاريخ.</small><button type="button" id="downloadHistoryComparison" class="secondary">تنزيل نتيجة المقارنة JSON</button></article>`;
}
function findStrings(bytes){const out=[];let cur=[];for(const b of bytes){if(b>=32&&b<=126)cur.push(b);else{if(cur.length>=5)out.push(String.fromCharCode(...cur));cur=[];}}if(cur.length>=5)out.push(String.fromCharCode(...cur));return out;}
function readUleb(bytes,state){let value=0,shift=0;for(let i=0;i<5;i++){if(state.p>=bytes.length)throw Error('ULEB128 خارج حدود DEX.');const b=bytes[state.p++];value|=(b&0x7f)<<shift;if(!(b&0x80))return value>>>0;shift+=7;}throw Error('ULEB128 غير صالح.');}
function parseDex(bytes){
 const v=new DataView(bytes.buffer,bytes.byteOffset,bytes.byteLength);if(bytes.length<112)throw Error('ملف DEX أقصر من الترويسة القياسية.');
 const magic=new TextDecoder().decode(bytes.slice(0,8));if(!/^dex\n0(3[5-9]|4[0-1])\0$/.test(magic))throw Error('توقيع DEX غير معروف.');
 const fileSize=u32(v,32),headerSize=u32(v,36),endian=u32(v,40);if(fileSize!==bytes.length||headerSize!==112||endian!==0x12345678)throw Error('ترويسة DEX أو الحجم أو ترتيب البايتات غير صالح.');
 const tables=[['string',56,60,4],['type',64,68,4],['proto',72,76,12],['field',80,84,8],['method',88,92,8],['class',96,100,32]];
 const meta={magic:magic.replace(/\0$/,''),fileSize,headerSize,checksum:u32(v,8).toString(16).padStart(8,'0'),strings:0,types:0,protos:0,fields:0,methods:0,classes:0};
 for(const [name,sizeAt,offAt,width] of tables){const count=u32(v,sizeAt),off=u32(v,offAt);meta[name==='string'?'strings':name==='type'?'types':name==='proto'?'protos':name==='field'?'fields':name==='method'?'methods':'classes']=count;if(count>2000000||(count&&(!off||off+count*width>bytes.length)))throw Error(`جدول ${name} في DEX خارج حدود الملف.`);}
 const count=meta.strings,off=u32(v,60),out=[];for(let i=0;i<count;i++){const dataOff=u32(v,off+i*4);if(dataOff>=bytes.length)throw Error('إزاحة سلسلة DEX غير صالحة.');const st={p:dataOff};readUleb(bytes,st);const start=st.p;while(st.p<bytes.length&&bytes[st.p]!==0)st.p++;if(st.p>=bytes.length)throw Error('سلسلة DEX غير منتهية.');const raw=bytes.slice(start,st.p);let text=new TextDecoder('utf-8').decode(raw);text=text.replace(/\\u0000/g,'');if(text.length>=2)out.push(text);}
 return {meta,strings:out};
}
async function analyze(file){
 if(file.size>LIMITS.file)throw Error('تجاوز الملف الحد الأقصى 512 MB.');
 const buf=await file.arrayBuffer(),hash=await sha(buf),entries=parseZip(buf),names=entries.map(e=>e.name),archiveAudit=auditArchive(entries);
 const dex=entries.filter(e=>/^classes(?:\d+)?\.dex$/i.test(e.name));
 const native=entries.filter(e=>/^lib\/[^/]+\/[^/]+\.so$/i.test(e.name));
 const manifest=entries.find(e=>e.name==='AndroidManifest.xml');
 let manifestData=null,manifestError='';if(manifest){try{manifestData=parseBinaryManifest(await extractEntry(manifest,buf,8*1024*1024));}catch(err){manifestError=err.message;}}
 const signing=detectApkSignatures(buf,entries);
 const certificateEntries=entries.filter(e=>/^META-INF\/[^/]+\.(RSA|DSA|EC)$/i.test(e.name));signing.certificates=[];for(const certEntry of certificateEntries.slice(0,20)){try{const certBytes=await extractEntry(certEntry,buf,8*1024*1024);signing.certificates.push(...await inspectX509Certificates(certBytes,certEntry.name));}catch(err){signing.certificateErrors??=[];signing.certificateErrors.push(`${certEntry.name}: ${err.message}`);}}
 const dexStrings=[],dexDetails=[];let totalDex=0;
 for(const e of dex){if(e.uncompressedSize>LIMITS.dex){dexDetails.push({name:e.name,valid:false,error:'يتجاوز حد قراءة DEX الآمن'});continue;}if(totalDex+e.uncompressedSize>LIMITS.totalDex)break;try{const raw=await extractEntry(e,buf,LIMITS.dex);totalDex+=e.uncompressedSize;const parsed=parseDex(raw);dexStrings.push(...parsed.strings);dexDetails.push({name:e.name,valid:true,...parsed.meta});}catch(err){dexDetails.push({name:e.name,valid:false,error:err.message});}}
 const permissions=PERMISSION_TOKENS.filter(token=>dexStrings.some(s=>s.includes(token)));
 const indicators=INDICATOR_TOKENS.filter(token=>dexStrings.some(s=>s.toLowerCase().includes(token.toLowerCase())));
 const suspiciousFiles=names.filter(n=>/\.((dex|so|jar|apk|sh|bin))$/i.test(n)||/\/assets\//i.test(n)).slice(0,100);
 const findings=[];
 for(const cert of signing.certificates||[]){if(cert.validity==='expired')findings.push({severity:'متوسط',weight:8,code:'SIGNING_CERTIFICATE_EXPIRED',detail:`شهادة التوقيع المستخرجة من ${cert.source} منتهية الصلاحية وفق تاريخ الجهاز؛ لا يعني ذلك وحده أن توقيع APK غير صالح وقت إنشائه.`});else if(cert.validity==='not-yet-valid')findings.push({severity:'مراجعة',weight:5,code:'SIGNING_CERTIFICATE_NOT_YET_VALID',detail:`تاريخ بدء صلاحية شهادة ${cert.source} يقع في المستقبل.`});}
 if(archiveAudit.duplicateNames.length)findings.push({severity:'مرتفع',weight:20,code:'DUPLICATE_ZIP_ENTRIES',detail:`توجد أسماء ملفات مكررة داخل الأرشيف (${archiveAudit.duplicateNames.length})؛ قد تسبب اختلافاً بين أدوات فك الضغط.`});
 if(archiveAudit.unsafePaths.length)findings.push({severity:'مرتفع',weight:20,code:'UNSAFE_ARCHIVE_PATHS',detail:`توجد مسارات مطلقة أو تتضمن ../ داخل الأرشيف (${archiveAudit.unsafePaths.length}).`});
 if(archiveAudit.highCompressionRatio.length)findings.push({severity:'متوسط',weight:12,code:'HIGH_COMPRESSION_RATIO',detail:`توجد عناصر بنسبة ضغط مرتفعة جداً (${archiveAudit.highCompressionRatio.length})؛ راجعها لاحتمال استهلاك موارد عند فك الضغط.`});
 if(archiveAudit.overlappingEntries.length)findings.push({severity:'مرتفع',weight:25,code:'OVERLAPPING_ZIP_ENTRIES',detail:'توجد مناطق بيانات متداخلة بين عناصر ZIP؛ قد تختلف طريقة تفسير الأرشيف بين الأدوات.'});
 if(archiveAudit.totalUncompressedBytes>2*1024*1024*1024)findings.push({severity:'مرتفع',weight:20,code:'EXCESSIVE_UNCOMPRESSED_SIZE',detail:'الحجم الإجمالي بعد فك الضغط يتجاوز 2 GiB؛ يلزم الحذر من استهلاك الموارد.'});
 if(archiveAudit.unsupportedCompression.length)findings.push({severity:'معلوماتي',weight:2,code:'UNSUPPORTED_COMPRESSION',detail:'توجد عناصر تستخدم طرق ضغط لا يدعم المحلل فكها حالياً.'});
 if(manifestData){
  const m=manifestData;
  if(m.application.debuggable==='true')findings.push({severity:'مرتفع',weight:25,code:'DEBUGGABLE',detail:'التطبيق يسمح بتصحيح الأخطاء (debuggable=true).'});
  if(m.application.usesCleartextTraffic==='true')findings.push({severity:'متوسط',weight:12,code:'CLEARTEXT_TRAFFIC',detail:'السماح بحركة HTTP غير المشفرة مفعّل.'});
  if(m.application.allowBackup==='true')findings.push({severity:'معلوماتي',weight:3,code:'ALLOW_BACKUP',detail:'نسخ بيانات التطبيق الاحتياطية مسموح به؛ راجع حساسية البيانات وسياسات النسخ.'});
  for(const c of m.components)if(c.exported==='true'&&!c.permission)findings.push({severity:'متوسط',weight:10,code:'EXPORTED_COMPONENT',detail:`${c.type} ${c.name} مصدّر دون permission معلنة؛ تحقق من ضرورة إتاحته.`});
  if(m.permissions.some(x=>/READ_SMS|SEND_SMS|RECEIVE_SMS|READ_CALL_LOG|WRITE_CALL_LOG|RECORD_AUDIO|CAMERA|ACCESS_FINE_LOCATION/.test(x)))findings.push({severity:'مراجعة',weight:7,code:'SENSITIVE_PERMISSION',detail:'توجد صلاحيات حساسة؛ تحقق من توافقها مع وظائف التطبيق.'});
  if(m.permissions.includes('android.permission.REQUEST_INSTALL_PACKAGES'))findings.push({severity:'متوسط',weight:10,code:'REQUEST_INSTALL_PACKAGES',detail:'التطبيق يطلب إمكانية طلب تثبيت حزم أخرى؛ تحقق من سبب الحاجة.'});
  if(m.permissions.includes('android.permission.SYSTEM_ALERT_WINDOW'))findings.push({severity:'متوسط',weight:10,code:'OVERLAY_PERMISSION',detail:'التطبيق يطلب صلاحية الظهور فوق التطبيقات الأخرى.'});
 }
 const has=t=>dexStrings.some(x=>x.toLowerCase().includes(t.toLowerCase()));
 if(has('DexClassLoader')||has('PathClassLoader'))findings.push({severity:'مراجعة',weight:8,code:'DYNAMIC_CODE_LOADING',detail:'ظهرت سلاسل مرتبطة بتحميل كود ديناميكي؛ قد تستخدمها تطبيقات مشروعة أيضاً.'});
 if(has('Runtime.getRuntime')||has('ProcessBuilder'))findings.push({severity:'مراجعة',weight:8,code:'PROCESS_EXECUTION_API',detail:'ظهرت سلاسل مرتبطة بإنشاء عمليات نظام؛ يلزم فحص السياق البرمجي.'});
 if(has('SmsManager')||has('sendTextMessage'))findings.push({severity:'مراجعة',weight:8,code:'SMS_API_REFERENCE',detail:'ظهرت سلاسل مرتبطة بواجهات SMS؛ ليست دليلاً على إرسال رسائل فعلياً.'});
 if(has('AccessibilityService'))findings.push({severity:'مراجعة',weight:8,code:'ACCESSIBILITY_API_REFERENCE',detail:'ظهرت إشارة إلى خدمات إمكانية الوصول؛ تحقق من الاستخدام المعلن للمستخدم.'});
 if(has('/system/bin/su')||has('su -c'))findings.push({severity:'متوسط',weight:12,code:'ROOT_COMMAND_REFERENCE',detail:'ظهرت سلسلة مرتبطة بأوامر root؛ قد تكون لأغراض إدارية أو اختبارية.'});
 if(has('http://'))findings.push({severity:'مراجعة',weight:5,code:'HTTP_STRING_REFERENCE',detail:'ظهرت عناوين HTTP نصية غير مشفرة داخل DEX؛ تحقق من الوجهة والاستخدام.'});
 const riskScore=Math.min(100,findings.reduce((n,f)=>n+f.weight,0));
 const riskLevel=riskScore>=50?'مرتفع':riskScore>=25?'متوسط':riskScore>=10?'منخفض':'مؤشرات محدودة';
 return {name:file.name,size:file.size,hash,entries:names.length,archiveAudit,signing,manifestData,manifestError,findings,riskScore,riskLevel,dex:dex.map(e=>({name:e.name,size:e.uncompressedSize,compressed:e.compressedSize})),dexDetails,native:native.map(e=>e.name),embeddedApk:names.filter(n=>/\.apk$/i.test(n)),manifestPresent:!!manifest,manifestBytes:manifest?.uncompressedSize??0,permissions,indicators,files:names.slice(0,500),suspiciousFiles,strings:dexStrings.length,notes:['الصلاحيات الموثوقة في التقرير مستخرجة من AndroidManifest.xml؛ مؤشرات DEX النصية منفصلة وقد تكون ناقصة.','التحليل ساكن ولا يشغّل التطبيق ولا يفك جميع تعليمات DEX.','درجة المخاطر إرشادية مبنية على قواعد بسيطة وليست احتمالاً إحصائياً أو حكماً بأن التطبيق خبيث.','عدم ظهور مؤشر لا يعني أن التطبيق آمن.']};
}
function render(r,index=0){const grid=[['الحجم',fmt(r.size)],['SHA-256',r.hash],['عناصر ZIP',r.entries],['سلامة بنية الأرشيف',r.archiveAudit?.structurallyReviewable?'لا توجد مؤشرات بنيوية محددة':'تحتاج مراجعة'],['ملفات DEX',r.dex.length],['DEX صالح',r.dexDetails.filter(d=>d.valid).length],['طرق DEX',r.dexDetails.reduce((n,d)=>n+(d.methods||0),0)],['مكتبات Native',r.native.length],['APK مضمّن',r.embeddedApk.length],['Manifest',r.manifestPresent?`موجود (${fmt(r.manifestBytes)})`:'غير موجود'],['سلاسل DEX',r.strings],['مؤشر المراجعة',`${r.riskScore}/100 · ${r.riskLevel}`],['توقيع V1',r.signing?.schemes.v1?'ملفات توقيع موجودة':'لم تُرصد'],['Signing Block',r.signing?.schemes.v2v3BlockPresent?'موجود':'لم يُرصد'],['شهادات X.509',r.signing?.certificates?.length||0]];
 return `<article class="card report-card" data-report-index="${index}"><div class="report-heading"><h3>${esc(r.name)}</h3><button type="button" class="ghost danger delete-report" data-delete-report="${index}" aria-label="حذف تقرير ${esc(r.name)}">حذف التقرير ×</button></div><div class="grid">${grid.map(([a,b])=>`<div class="item"><small>${a}</small><b>${esc(b)}</b></div>`).join('')}</div><h4>تدقيق بنية الأرشيف</h4><p>أسماء مكررة: ${r.archiveAudit?.duplicateNames.length||0} · مسارات غير آمنة: ${r.archiveAudit?.unsafePaths.length||0} · نسب ضغط مرتفعة: ${r.archiveAudit?.highCompressionRatio.length||0} · تداخلات: ${r.archiveAudit?.overlappingEntries.length||0} · إجمالي الحجم بعد فك الضغط: ${fmt(r.archiveAudit?.totalUncompressedBytes||0)}</p><h4>مؤشرات توقيع APK</h4><p>ملفات META-INF: ${r.signing?.v1Files.length?esc(r.signing.v1Files.join(' · ')):'لم تُرصد'}<br>${esc(r.signing?.verification||'')}</p><small>${(r.signing?.limitations||[]).map(esc).join(' ')}</small><h4>شهادات X.509 المكتشفة</h4><p>${(r.signing?.certificates||[]).map(c=>`${esc(c.subject)} · تنتهي: ${esc(c.notAfter)} · SHA-256: ${esc(c.sha256)}`).join('<br>')||'لم يتم استخراج شهادة DER قابلة للتفسير من ملفات التوقيع.'}</p><h4>بيانات Manifest الفعلية</h4>${r.manifestData?`<p>الحزمة: <b dir="ltr">${esc(r.manifestData.packageName||'غير محدد')}</b> · الإصدار: ${esc(r.manifestData.versionName||'غير محدد')} · SDK: ${esc(r.manifestData.minSdk||'?')} / ${esc(r.manifestData.targetSdk||'?')}</p><p>الصلاحيات: ${r.manifestData.permissions.length?esc(r.manifestData.permissions.join(' · ')):'لا توجد صلاحيات معلنة'}</p><p>مكونات التطبيق: ${r.manifestData.components.length} · Debuggable: ${esc(r.manifestData.application.debuggable)} · Allow backup: ${esc(r.manifestData.application.allowBackup)} · Cleartext: ${esc(r.manifestData.application.usesCleartextTraffic)}</p><details><summary>المكونات (${r.manifestData.components.length})</summary><p dir="ltr">${r.manifestData.components.map(c=>esc(`${c.type}: ${c.name} | exported=${c.exported}`)).join('<br>')}</p></details>`:esc(r.manifestError||'تعذر استخراج Manifest')}<h4>مؤشرات صلاحيات نصية من DEX (ثانوية)</h4><p>${r.permissions.length?esc(r.permissions.join(' · ')):'لم تُرصد ضمن النصوص المفحوصة'}</p><h4>مؤشر المخاطر الإرشادي</h4><p><b>${r.riskScore}/100 · ${esc(r.riskLevel)}</b> — لا يمثل حكماً نهائياً على سلامة التطبيق.</p><h4>نتائج مراجعة ثابتة (ليست حكماً أمنياً)</h4><p>${r.findings.length?r.findings.map(f=>`<span class="badge">${esc(f.severity)} · ${esc(f.code)}</span> ${esc(f.detail)}`).join('<br>'):'لم تُفعّل قواعد المراجعة المحددة.'}</p><h4>بنية DEX</h4><p>${r.dexDetails.map(d=>esc(`${d.name}: ${d.valid?`${d.magic} · strings=${d.strings} · methods=${d.methods} · classes=${d.classes}`:`غير صالح/غير مقروء (${d.error})`}`)).join('<br>')||'لا توجد ملفات DEX'}</p><h4>مؤشرات تقنية</h4><p>${r.indicators.length?esc(r.indicators.join(' · ')):'لم تُرصد المؤشرات المحددة'}</p><details><summary>ملفات قد تستحق المراجعة (${r.suspiciousFiles.length})</summary><p dir="ltr">${r.suspiciousFiles.map(esc).join('<br>')}</p></details><details><summary>أسماء الملفات (${r.files.length} من ${r.entries})</summary><p dir="ltr">${r.files.map(esc).join('<br>')}</p></details><small>${r.notes.map(esc).join(' ')}</small></article>`;
}
function buildDashboardStats(items){
 const valid=items.filter(Boolean),count=valid.length;
 const average=count?Math.round(valid.reduce((n,r)=>n+(Number(r.riskScore)||0),0)/count):0;
 const elevated=valid.filter(r=>(Number(r.riskScore)||0)>=25).length;
 const packages=new Set(valid.map(r=>r.manifestData?.packageName).filter(Boolean)).size;
 const permissions=new Set(valid.flatMap(r=>r.manifestData?.permissions||[])).size;
 return {count,average,elevated,packages,permissions};
}
function prepareBatch(files,currentCount=0){
 const selected=[...files].filter(f=>/\.apk$/i.test(f.name)||f.type==='application/vnd.android.package-archive');
 const available=Math.max(0,LIMITS.sessionReports-currentCount);
 return {selectedCount:selected.length,queue:selected.slice(0,Math.min(LIMITS.batch,available)),limit:LIMITS.batch,available};
}
function dashboardRender(){
 const el=$('dashboard');if(!el)return;const s=buildDashboardStats(reports);
 el.innerHTML=[['ملفات في الجلسة',s.count],['متوسط مؤشر المراجعة',`${s.average}/100`],['تحتاج مراجعة أعمق',s.elevated],['حزم مختلفة',s.packages],['صلاحيات فريدة',s.permissions]].map(([k,v])=>`<div class="dash-item"><small>${k}</small><b>${esc(v)}</b></div>`).join('');
}
function sessionControlsRender(){
 const count=reports.length,has= count>0;
 $('count').textContent=count;
 for(const id of ['export','exportJson','exportCsv','printReport','exportHtmlReport']){const el=$(id);if(el)el.disabled=!has;}
 const compare=$('compare');if(compare)compare.disabled=count<2;
 const clear=$('clear');if(clear)clear.disabled=!has;
 dashboardRender();
}
function clearSessionReports(){
 reports.length=0;
 $('results').innerHTML='<div class="empty"><span>⌁</span><b>لا توجد نتائج بعد</b><small>ابدأ باختيار ملف APK لتحصل على تقرير التحليل.</small></div>';
 $('last').textContent='—';sessionControlsRender();$('status').textContent='تم مسح تقارير الجلسة؛ سجل التحليلات المحفوظ لم يتغير.';
}
async function processFiles(files){
 const batch=prepareBatch(files,reports.length),queue=batch.queue;
 if(!batch.selectedCount){$('status').textContent='لم يتم اختيار ملفات APK صالحة';return;}
 if(!queue.length){$('status').textContent='بلغت الجلسة الحد الأقصى وهو 50 تقريراً؛ امسح النتائج لبدء جلسة جديدة.';return;}
 if(batch.selectedCount>queue.length)$('status').textContent=`سيتم تحليل ${queue.length} من ${batch.selectedCount} ملفاً؛ الحد 20 لكل دفعة و50 لكل جلسة.`;
 for(let i=0;i<queue.length;i++){
  const file=queue[i];$('status').textContent=`جارٍ التحليل ${i+1}/${queue.length}: ${file.name}`;
  try{const r=await analyze(file);reports.push(r);historySave(r);}
  catch(e){$('results').insertAdjacentHTML('beforeend',`<div class="card error">تعذر تحليل ${esc(file.name)}: ${esc(e.message)}</div>`);}
  const errors=[...$('results').querySelectorAll('.error')].map(node=>node.outerHTML).join('');$('results').innerHTML=reports.map((report,index)=>render(report,index)).join('')+errors;
  $('last').textContent=new Date().toLocaleTimeString('ar');sessionControlsRender();
 }
 $('status').textContent=`اكتمل تحليل ${queue.length} ملفاً`;
 sessionControlsRender();
}

function download(content,name,type){const url=URL.createObjectURL(new Blob([content],{type})),a=document.createElement('a');a.href=url;a.download=name;a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);}
function csvCell(v){let value=String(v??'');if(/^[\s]*[=+@\-\t\r]/.test(value))value="'"+value;return '"'+value.replace(/"/g,'""')+'"';}
$('pick').onclick=()=>$('files').click();$('files').onchange=e=>{processFiles(e.target.files);e.target.value='';};$('drop').onclick=()=>$('files').click();$('drop').ondragover=e=>{e.preventDefault();$('drop').classList.add('over');};$('drop').ondragleave=()=>$('drop').classList.remove('over');$('drop').ondrop=e=>{e.preventDefault();$('drop').classList.remove('over');processFiles(e.dataTransfer.files);};
$('clearHistory').onclick=()=>{const settings=settingsLoad();if(settings.confirmHistoryClear&&!confirm('هل تريد مسح سجل التحليلات المحفوظ بالكامل؟ لا يمكن التراجع عن هذه العملية.'))return;try{localStorage.removeItem('asl.analysis.history');historyRender();$('status').textContent='تم مسح سجل التحليلات المحفوظ.';}catch{$('status').textContent='تعذر مسح السجل المحفوظ.';}};
$('history').addEventListener('click',e=>{const button=e.target.closest('[data-delete-history]');if(!button)return;const hash=button.dataset.deleteHistory;if(!/^[a-f0-9]{64}$/i.test(hash))return;const item=historyLoad().find(x=>x.hash===hash);if(!item)return;if(!confirm(`هل تريد حذف سجل التحليل الخاص بـ ${item.name||'هذا الملف'}؟`))return;if(historyDelete(hash))$('status').textContent='تم حذف السجل المحدد من هذا الجهاز.';});
$('historySearch').oninput=historyRender;
const compactControl=$('compactMode'),confirmControl=$('confirmHistoryClear'),resetControl=$('resetSettings');
if(compactControl)compactControl.onchange=settingsSave;if(confirmControl)confirmControl.onchange=settingsSave;
if(resetControl)resetControl.onclick=()=>{try{localStorage.setItem(SETTINGS_KEY,JSON.stringify(DEFAULT_SETTINGS));settingsApply(DEFAULT_SETTINGS);$('status').textContent='تمت استعادة الإعدادات الافتراضية.';}catch{$('status').textContent='تعذرت استعادة الإعدادات.';}};
settingsApply();
$('exportHistory').onclick=()=>{const items=historyLoad(),rows=[['name','package_name','version','size_bytes','sha256','risk_score','risk_level','analyzed_at'],...items.map(x=>[x.name,x.packageName,x.version,x.size,x.hash,x.riskScore,x.riskLevel,x.analyzedAt])];download('\ufeff'+rows.map(row=>row.map(csvCell).join(',')).join('\r\n'),'ASL-history.csv','text/csv;charset=utf-8');};
$('backupHistory').onclick=async()=>{const items=historyLoad();if(!items.length)return;try{const backup=await createHistoryBackup(items);download(JSON.stringify(backup,null,2),'ASL-history-backup.json','application/json;charset=utf-8');$('status').textContent='تم إنشاء نسخة احتياطية مع بصمة SHA-256 للتحقق من سلامتها.';}catch(err){$('status').textContent=`تعذر إنشاء النسخة الاحتياطية: ${err.message}`;}};
$('importHistory').onclick=()=>$('historyFile').click();
$('historyFile').onchange=async e=>{const file=e.target.files?.[0];e.target.value='';try{const result=await importHistoryBackup(file);$('status').textContent=`تم استيراد ${result.imported} سجلاً؛ الإجمالي ${result.total}.`; }catch(err){$('status').textContent=`تعذرت الاستعادة: ${err.message}`;}};
$('historyBase').onchange=historyRender;$('historyTarget').onchange=historyRender;
$('compareHistory').onclick=()=>{try{const items=historyLoad(),base=items.find(x=>x.hash===$('historyBase').value),target=items.find(x=>x.hash===$('historyTarget').value),comparison=compareHistoryRecords(base,target);$('results').insertAdjacentHTML('afterbegin',renderHistoryComparison(comparison));$('downloadHistoryComparison').onclick=()=>download(JSON.stringify(comparison,null,2),'ASL-history-comparison.json','application/json;charset=utf-8');$('status').textContent='اكتملت مقارنة السجلين؛ البيانات المتاحة وصفية ومختصرة.';}catch(err){$('status').textContent=`تعذرت المقارنة: ${err.message}`;}};
historyRender();sessionControlsRender();
$('clear').onclick=()=>{if(!reports.length)return;if(confirm('هل تريد حذف جميع تقارير الجلسة الحالية؟ لن يتم حذف سجل التحليلات المحفوظ.'))clearSessionReports();};
$('results').addEventListener('click',e=>{const button=e.target.closest('[data-delete-report]');if(!button)return;const index=Number(button.dataset.deleteReport);if(!Number.isInteger(index)||index<0||index>=reports.length)return;const name=reports[index].name||'هذا التقرير';if(!confirm(`هل تريد حذف التقرير: ${name}؟`))return;reports.splice(index,1);$('results').innerHTML=reports.length?reports.map((report,i)=>render(report,i)).join(''):'<div class="empty"><span>⌁</span><b>لا توجد نتائج بعد</b><small>ابدأ باختيار ملف APK لتحصل على تقرير التحليل.</small></div>';sessionControlsRender();$('status').textContent='تم حذف التقرير من الجلسة؛ سجل التحليلات المحفوظ لم يتغير.';});
$('export').onclick=()=>download('ABDELLATIF SECURITY LAB\n'+new Date().toISOString()+'\n\n'+reports.map(r=>JSON.stringify(r,null,2)).join('\n\n'),'ASL-report.txt','text/plain;charset=utf-8');
$('exportJson').onclick=()=>download(JSON.stringify({tool:'ABDELLATIF SECURITY LAB',generatedAt:new Date().toISOString(),reports},null,2),'ASL-report.json','application/json;charset=utf-8');
$('exportCsv').onclick=()=>{const rows=[['name','size_bytes','sha256','zip_entries','dex_count','native_count','embedded_apk_count','manifest_present','package_name','version_name','min_sdk','target_sdk','manifest_permissions','risk_score','risk_level','finding_count','finding_codes','component_count','debuggable','allow_backup','cleartext_traffic','permissions_text_hits','indicators']];for(const r of reports)rows.push([r.name,r.size,r.hash,r.entries,r.dex.length,r.native.length,r.embeddedApk.length,r.manifestPresent,r.manifestData?.packageName||'',r.manifestData?.versionName||'',r.manifestData?.minSdk||'',r.manifestData?.targetSdk||'',r.manifestData?.permissions.join('; ')||'',r.riskScore,r.riskLevel,r.findings.length,r.findings.map(f=>f.code).join('; '),r.manifestData?.components.length||0,r.manifestData?.application.debuggable||'',r.manifestData?.application.allowBackup||'',r.manifestData?.application.usesCleartextTraffic||'',r.permissions.join('; '),r.indicators.join('; ')]);download('\ufeff'+rows.map(row=>row.map(csvCell).join(',')).join('\r\n'),'ASL-report.csv','text/csv;charset=utf-8');};

function buildStandaloneHtmlReport(items,generatedAt=new Date().toISOString()){
 const sections=items.map((r,index)=>{
  const permissions=r.manifestData?.permissions||[];
  const components=r.manifestData?.components||[];
  const findings=r.findings||[];
  const dex=r.dexDetails||[];
  const list=(values,empty='لا توجد بيانات')=>values.length?`<ul>${values.map(x=>`<li>${esc(x)}</li>`).join('')}</ul>`:`<p>${empty}</p>`;
  return `<section class="report"><h2>${index+1}. ${esc(r.name||'APK')}</h2><div class="grid"><div><small>SHA-256</small><code>${esc(r.hash||'')}</code></div><div><small>الحجم</small><b>${fmt(Number(r.size)||0)}</b></div><div><small>مؤشر المراجعة</small><b>${Number(r.riskScore)||0}/100 · ${esc(r.riskLevel||'غير محدد')}</b></div><div><small>عناصر ZIP</small><b>${Number(r.entries)||0}</b></div></div><h3>بيانات التطبيق</h3><p>الحزمة: <code>${esc(r.manifestData?.packageName||'غير متاح')}</code> · الإصدار: ${esc(r.manifestData?.versionName||'غير متاح')} · SDK: ${esc(r.manifestData?.minSdk||'?')} / ${esc(r.manifestData?.targetSdk||'?')}</p><h3>الصلاحيات</h3>${list(permissions)}<h3>المكونات</h3>${list(components.map(c=>`${c.type}: ${c.name} · exported=${c.exported} · permission=${c.permission||'—'}`))}<h3>مراجعة بنية ZIP</h3><p>أسماء مكررة: ${(r.archiveAudit?.duplicateNames||[]).length} · مسارات غير آمنة: ${(r.archiveAudit?.unsafePaths||[]).length} · نسب ضغط مرتفعة: ${(r.archiveAudit?.highCompressionRatio||[]).length} · تداخلات: ${(r.archiveAudit?.overlappingEntries||[]).length}</p><h3>التوقيع والشهادات</h3><p>V1: ${r.signing?.schemes?.v1?'مرصود':'غير مرصود'} · Signing Block V2/V3: ${r.signing?.schemes?.v2v3BlockPresent?'مرصود':'غير مرصود'}</p>${list((r.signing?.certificates||[]).map(c=>`Subject: ${c.subject}; Issuer: ${c.issuer}; SHA-256: ${c.sha256}; validity: ${c.validity}`),'لم يتم استخراج شهادة قابلة للقراءة')}<h3>ملفات DEX</h3>${list(dex.map(d=>`${d.name}: ${d.valid?'صالح':'غير صالح'} · strings=${d.strings||0} · methods=${d.methods||0} · classes=${d.classes||0} ${d.error||''}`),'لا توجد ملفات DEX')}<h3>نتائج المراجعة</h3>${findings.length?`<ul>${findings.map(f=>`<li><b>${esc(f.severity)} · ${esc(f.code)}</b>: ${esc(f.detail)}</li>`).join('')}</ul>`:'<p>لم تُفعّل قواعد المراجعة المحددة.</p>'}<h3>ملاحظات وحدود التحليل</h3>${list(r.notes||[],'لا توجد ملاحظات')}</section>`;
 }).join('');
 return `<!doctype html><html lang="ar" dir="rtl"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'"><title>ASL - تقرير التحليل</title><style>body{font:15px/1.85 Arial,sans-serif;margin:24px auto;padding:0 18px;max-width:1050px;color:#17212b;background:#f4f7fa}header,.report{background:#fff;border:1px solid #dbe4eb;border-radius:14px;padding:22px;margin:18px 0}h1,h2{color:#123b57}h2{border-bottom:2px solid #1b7894;padding-bottom:10px}h3{color:#17627b;margin-top:24px}.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(190px,1fr));gap:10px}.grid>div{background:#f2f6f8;padding:12px;border-radius:8px}small{display:block;color:#61717d}code{direction:ltr;unicode-bidi:plaintext;overflow-wrap:anywhere}.note{background:#fff4d6;padding:12px;border-radius:8px}@media print{body{background:#fff;margin:0}.report{break-after:page;border:0}header,.report{box-shadow:none}}</style></head><body><header><h1>ABDELLATIF SECURITY LAB</h1><p>تقرير تحليل ساكن لملفات APK</p><small>تاريخ الإنشاء: ${esc(generatedAt)} · عدد التقارير: ${items.length}</small><p class="note">هذا التقرير يعرض مؤشرات ساكنة فقط. لا يثبت خلو التطبيق من البرمجيات الخبيثة ولا يمثل تحققاً تشفيرياً كاملاً من التوقيع.</p><button onclick="window.print()">طباعة / حفظ PDF</button></header>${sections}</body></html>`;
}
const htmlReportButton=$('exportHtmlReport');if(htmlReportButton)htmlReportButton.onclick=()=>{if(!reports.length)return;download(buildStandaloneHtmlReport(reports),'ASL-security-report.html','text/html;charset=utf-8');$('status').textContent='تم تنزيل تقرير HTML مستقل؛ افتحه في المتصفح ثم اختر طباعة / حفظ PDF.';};

$('printReport').onclick=()=>{
 const rows=reports.map(r=>`<section><h2>${esc(r.name)}</h2><p><b>SHA-256:</b> <code>${esc(r.hash)}</code></p><p>الحجم: ${fmt(r.size)} · عناصر ZIP: ${r.entries} · مؤشر المراجعة: ${r.riskScore}/100 (${esc(r.riskLevel)})</p><h3>تدقيق ZIP</h3><p>أسماء مكررة: ${r.archiveAudit?.duplicateNames.length||0} · مسارات غير آمنة: ${r.archiveAudit?.unsafePaths.length||0} · نسب ضغط مرتفعة: ${r.archiveAudit?.highCompressionRatio.length||0} · تداخلات: ${r.archiveAudit?.overlappingEntries.length||0}</p><h3>Manifest</h3><p>الحزمة: <code>${esc(r.manifestData?.packageName||'غير متاح')}</code> · الإصدار: ${esc(r.manifestData?.versionName||'غير متاح')}</p><p>الصلاحيات: ${esc(r.manifestData?.permissions.join('، ')||'غير متاح')}</p><p>المكونات: ${r.manifestData?.components.length??0} · Debuggable: ${esc(r.manifestData?.application.debuggable||'غير متاح')} · Cleartext: ${esc(r.manifestData?.application.usesCleartextTraffic||'غير متاح')}</p><h3>التوقيع</h3><p>V1: ${r.signing?.schemes.v1?'ملفات توقيع مرصودة':'غير مرصود'} · V2/V3 Signing Block: ${r.signing?.schemes.v2v3BlockPresent?'مرصود':'غير مرصود'}</p><p>${esc(r.signing?.verification||'')}</p><ul>${(r.signing?.certificates||[]).map(c=>`<li>Subject: ${esc(c.subject)} · Issuer: ${esc(c.issuer)} · Serial: ${esc(c.serial)} · Validity: ${esc(c.notBefore)} → ${esc(c.notAfter)} (${esc(c.validity)}) · SHA-256: ${esc(c.sha256)}</li>`).join('')||'<li>لم تُستخرج شهادة X.509 قابلة للقراءة.</li>'}</ul><h3>DEX</h3><ul>${r.dexDetails.map(d=>`<li>${esc(d.name)} — ${d.valid?`صالح ${esc(d.magic)}؛ strings ${d.strings}؛ methods ${d.methods}؛ classes ${d.classes}`:`تعذر التحقق: ${esc(d.error)}`}</li>`).join('')}</ul><h3>نتائج المراجعة</h3><ul>${r.findings.map(f=>`<li><b>${esc(f.severity)} · ${esc(f.code)}</b>: ${esc(f.detail)}</li>`).join('')||'<li>لا توجد نتائج وفق القواعد الحالية.</li>'}</ul><h3>ملاحظات المنهجية</h3><ul>${r.notes.map(n=>`<li>${esc(n)}</li>`).join('')}</ul></section>`).join('');
 const w=window.open('','_blank');if(!w){$('status').textContent='يرجى السماح بالنوافذ المنبثقة لطباعة التقرير';return;}
 w.document.write(`<!doctype html><html lang="ar" dir="rtl"><meta charset="utf-8"><title>ASL Security Report</title><style>body{font:14px/1.8 Arial,sans-serif;margin:28px;color:#17212b}h1{color:#123b57}h2{border-bottom:2px solid #1b7894;padding-bottom:8px}section{page-break-after:always}code{direction:ltr;word-break:break-all}li{margin:5px 0}.meta{color:#52616b}@media print{button{display:none}}</style><h1>ABDELLATIF SECURITY LAB</h1><p class="meta">تقرير تحليل ساكن لملفات APK · ${new Date().toLocaleString('ar')}</p>${rows}<button onclick="window.print()">طباعة / حفظ PDF</button><script>setTimeout(()=>window.print(),500)<\/script></html>`);w.document.close();
};

function compareReports(a,b){
 const setDiff=(left,right)=>({added:right.filter(x=>!left.includes(x)),removed:left.filter(x=>!right.includes(x)),unchanged:left.filter(x=>right.includes(x))});
 const componentKey=c=>`${c.type}|${c.name}|${c.exported}|${c.permission||''}`;
 const findingKey=f=>`${f.code}|${f.severity}`;
 const dexNames=r=>r.dex.map(d=>d.name);
 const nativeNames=r=>r.native;
 const permissions=r=>r.manifestData?.permissions||[];
 const components=r=>(r.manifestData?.components||[]).map(componentKey);
 const findings=r=>(r.findings||[]).map(findingKey);
 const aPkg=a.manifestData?.packageName||'',bPkg=b.manifestData?.packageName||'';
 const aVersion=a.manifestData?.versionName||'',bVersion=b.manifestData?.versionName||'';
 return {
  tool:'ABDELLATIF SECURITY LAB',schemaVersion:'1.5',generatedAt:new Date().toISOString(),
  files:{a:{name:a.name,size:a.size,sha256:a.hash,packageName:aPkg,versionName:aVersion,riskScore:a.riskScore,riskLevel:a.riskLevel},b:{name:b.name,size:b.size,sha256:b.hash,packageName:bPkg,versionName:bVersion,riskScore:b.riskScore,riskLevel:b.riskLevel}},
  identity:{samePackage:!!aPkg&&aPkg===bPkg,packageChanged:aPkg!==bPkg,versionChanged:aVersion!==bVersion,identicalSha256:a.hash===b.hash},
  risk:{delta:b.riskScore-a.riskScore,direction:b.riskScore>a.riskScore?'increased':b.riskScore<a.riskScore?'decreased':'unchanged'},
  permissions:setDiff(permissions(a),permissions(b)),
  components:setDiff(components(a),components(b)),
  dexFiles:setDiff(dexNames(a),dexNames(b)),
  nativeLibraries:setDiff(nativeNames(a),nativeNames(b)),
  findings:setDiff(findings(a),findings(b)),
  summary:{permissionsAdded:setDiff(permissions(a),permissions(b)).added.length,permissionsRemoved:setDiff(permissions(a),permissions(b)).removed.length,componentsAdded:setDiff(components(a),components(b)).added.length,componentsRemoved:setDiff(components(a),components(b)).removed.length,dexAdded:setDiff(dexNames(a),dexNames(b)).added.length,dexRemoved:setDiff(dexNames(a),dexNames(b)).removed.length}
 };
}
function renderComparison(c){
 const rows=[['الحزمة نفسها',c.identity.samePackage?'نعم':'لا'],['تطابق SHA-256',c.identity.identicalSha256?'نعم':'لا'],['تغير الإصدار',c.identity.versionChanged?'نعم':'لا'],['تغير مؤشر المراجعة',`${c.risk.delta>0?'+':''}${c.risk.delta} نقطة`],['صلاحيات مضافة',c.summary.permissionsAdded],['صلاحيات محذوفة',c.summary.permissionsRemoved],['مكونات مضافة',c.summary.componentsAdded],['مكونات محذوفة',c.summary.componentsRemoved],['ملفات DEX مضافة',c.summary.dexAdded],['ملفات DEX محذوفة',c.summary.dexRemoved]];
 const list=(title,d)=>`<h4>${title}</h4><p>${d.length?d.map(esc).join('<br>'):'لا توجد تغييرات'}</p>`;
 return `<article class="card"><h3>نتيجة مقارنة الإصدارين</h3><div class="grid">${rows.map(([k,v])=>`<div class="item"><small>${k}</small><b>${esc(v)}</b></div>`).join('')}</div><h4>الصلاحيات</h4>${list('مضافة',c.permissions.added)}${list('محذوفة',c.permissions.removed)}<h4>المكونات (النوع | الاسم | exported | permission)</h4>${list('مضافة',c.components.added)}${list('محذوفة',c.components.removed)}<h4>ملفات DEX</h4>${list('مضافة',c.dexFiles.added)}${list('محذوفة',c.dexFiles.removed)}<h4>مكتبات Native</h4>${list('مضافة',c.nativeLibraries.added)}${list('محذوفة',c.nativeLibraries.removed)}<small>المقارنة وصفية بين البيانات المستخرجة فقط؛ لا تثبت سلامة التطبيق أو خبثه.</small></article>`;
}
$('compare').onclick=()=>{if(reports.length<2)return;const [a,b]=reports.slice(-2),comparison=compareReports(a,b);$('results').insertAdjacentHTML('afterbegin',renderComparison(comparison));download(JSON.stringify(comparison,null,2),'ASL-comparison.json','application/json;charset=utf-8');$('status').textContent='اكتملت المقارنة وتم تصدير JSON';};
let installPrompt;$('install').onclick=()=>installPrompt?.prompt();window.addEventListener('beforeinstallprompt',e=>{e.preventDefault();installPrompt=e;$('install').hidden=false;});if('serviceWorker'in navigator)window.addEventListener('load',()=>navigator.serviceWorker.register('./sw.js').catch(()=>{}));
