// 8085 WaveLab v0.1
// This first version supports the instructions used by the sample program
// plus a small useful set. It is an educational subset, not a complete 8085.

const $ = (id) => document.getElementById(id);
const exampleCode = `MVI A, 80H
OUT 03H
L3: XRA A
L1: OUT 00H
    INR A
    CPI FFH
    JNZ L1
L2: OUT 00H
    DCR A
    CPI 00H
    JNZ L2
    JMP L3`;

let cpu, program = [], labels = {}, chart, running = false, timer = null;
let samples = [], instructionCount = 0, lastInstruction = "Not started";
let assembledSnapshot = "";

const hex = (n, digits=2) => (n & 0xFFFF).toString(16).toUpperCase().padStart(digits, "0") + "H";
const byte = (n) => n & 0xFF;
const parseNumber = (raw) => {
  const s = raw.trim().toUpperCase();
  if (/^[0-9A-F]+H$/.test(s)) return parseInt(s.slice(0,-1),16);
  if (/^0X[0-9A-F]+$/.test(s)) return parseInt(s.slice(2),16);
  if (/^[0-9]+$/.test(s)) return parseInt(s,10);
  throw new Error(`Invalid number "${raw}"`);
};
const parity = (v) => (v.toString(2).replace(/0/g,"").length % 2) === 0;
const signed = (v) => (v & 0x80) !== 0;

function instructionSize(op, args) {
  if (["MVI","ADI","SUI","ANI","ORI","XRI","CPI","IN","OUT"].includes(op)) return 2;
  if (["LXI"].includes(op)) return 3;
  if (["JMP","JNZ","JZ","JC","JNC","CALL"].includes(op)) return 3;
  return 1;
}

function assemble(source, start) {
  const rawLines = source.split(/\r?\n/);
  const parsed = [];
  let address = start;
  const labelMap = {};
  for (let i=0; i<rawLines.length; i++) {
    let line = rawLines[i].split(";")[0].trim();
    if (!line) continue;
    let label = null;
    const match = line.match(/^([A-Za-z_][\w]*):\s*(.*)$/);
    if (match) { label = match[1].toUpperCase(); line = match[2].trim(); }
    if (label) {
      if (labelMap[label] !== undefined) throw new Error(`Line ${i+1}: Duplicate label ${label}`);
      labelMap[label] = address;
    }
    if (!line) continue;
    const parts = line.match(/^(\S+)(?:\s+(.*))?$/);
const op = parts[1].toUpperCase();

const operandText = (parts[2] || "").trim();

const args = operandText
    ? operandText.split(",").map(x => x.trim().toUpperCase())
    : [];
    const allowed = ["MVI","MOV","LXI","XRA","INR","DCR","CPI","OUT","IN","JNZ","JZ","JMP","JC","JNC","HLT","NOP","ADI","SUI","ANI","ORI","XRI"];
    if (!allowed.includes(op)) throw new Error(`Line ${i+1}: Unknown instruction "${op}"`);
    const expected = ({MVI:2,MOV:2,LXI:2,XRA:1,INR:1,DCR:1,CPI:1,OUT:1,IN:1,JNZ:1,JZ:1,JMP:1,JC:1,JNC:1,HLT:0,NOP:0,ADI:1,SUI:1,ANI:1,ORI:1,XRI:1})[op];
    if (args.length !== expected) throw new Error(`Line ${i+1}: ${op} expects ${expected} operand(s)`);
    const size = instructionSize(op,args);
    parsed.push({op,args,line:i+1,source:rawLines[i].trim(),address,size});
    address += size;
    if (address > 0x10000) throw new Error(`Line ${i+1}: Program exceeds 64 KB memory`);
  }
  for (const ins of parsed) {
    if (["JNZ","JZ","JMP","JC","JNC"].includes(ins.op)) {
      const target = ins.args[0];
      if (labelMap[target] === undefined) {
        try { const n=parseNumber(target); if(n>0xFFFF) throw new Error(); ins.target=n; }
        catch { throw new Error(`Line ${ins.line}: Unknown label or invalid address "${target}"`); }
      } else ins.target=labelMap[target];
    }
    if (ins.op==="OUT" || ins.op==="IN") {
      const p=parseNumber(ins.args[0]); if(p>255) throw new Error(`Line ${ins.line}: I/O port must be 00H–FFH`);
      ins.port=p;
    }
    if (ins.op==="MVI" && (!isRegister(ins.args[0]) || parseNumber(ins.args[1])>255)) throw new Error(`Line ${ins.line}: Invalid MVI operands`);
    if (["INR","DCR","XRA"].includes(ins.op) && !isRegister(ins.args[0])) throw new Error(`Line ${ins.line}: Invalid register`);
    if (ins.op==="CPI" && parseNumber(ins.args[0])>255) throw new Error(`Line ${ins.line}: CPI value must fit in 8 bits`);
    if (ins.op==="MOV" && (!isRegister(ins.args[0]) || !isRegister(ins.args[1]))) throw new Error(`Line ${ins.line}: MOV requires two registers`);
    if (ins.op==="LXI" && (!["B","D","H","SP"].includes(ins.args[0]) || parseNumber(ins.args[1])>65535)) throw new Error(`Line ${ins.line}: Invalid LXI operands`);
    if (["ADI","SUI","ANI","ORI","XRI"].includes(ins.op) && parseNumber(ins.args[0])>255) throw new Error(`Line ${ins.line}: Immediate value must fit in 8 bits`);
  }
  return {instructions:parsed, labels:labelMap};
}

function isRegister(r) { return ["A","B","C","D","E","H","L","M"].includes(r); }
function makeCPU(start) {
  return {r:{A:0,B:0,C:0,D:0,E:0,H:0,L:0}, PC:start, SP:0xFFFF,
    f:{S:0,Z:0,AC:0,P:0,CY:0}, halted:false, memory:new Uint8Array(65536), ports:new Uint8Array(256)};
}
function getReg(name) {
  if(name==="M") return cpu.memory[(cpu.r.H<<8)|cpu.r.L];
  return cpu.r[name];
}
function setReg(name,value) {
  value=byte(value);
  if(name==="M") cpu.memory[(cpu.r.H<<8)|cpu.r.L]=value;
  else cpu.r[name]=value;
}
function setSZP(v) { v=byte(v); cpu.f.S=signed(v)?1:0; cpu.f.Z=v===0?1:0; cpu.f.P=parity(v)?1:0; }
function fetchInstruction() { return program.find(x=>x.address===cpu.PC); }

function executeOne() {
  if(cpu.halted) return false;
  const ins=fetchInstruction();
  if(!ins) throw new Error(`Execution reached ${hex(cpu.PC,4)}, which is not a program instruction. Check your jump address.`);
  const [a,b]=ins.args; let next=cpu.PC+ins.size;
  lastInstruction=`${hex(ins.address,4)}  ${ins.source}`;
  switch(ins.op) {
    case "NOP": break;
    case "HLT": cpu.halted=true; break;
    case "MVI": setReg(a,parseNumber(b)); break;
    case "MOV": setReg(a,getReg(b)); break;
    case "LXI": { const v=parseNumber(b); if(a==="SP") cpu.SP=v; else {const pair={B:"C",D:"E",H:"L"};cpu.r[a]=v>>8;cpu.r[pair[a]]=v&255;} break; }
    case "XRA": { const v=cpu.r.A ^ getReg(a); cpu.r.A=byte(v); cpu.f.AC=0;cpu.f.CY=0;setSZP(v);break; }
    case "INR": { const old=getReg(a),v=byte(old+1); setReg(a,v); cpu.f.AC=(old&15)===15?1:0;setSZP(v);break; }
    case "DCR": { const old=getReg(a),v=byte(old-1); setReg(a,v); cpu.f.AC=(old&15)===0?1:0;setSZP(v);break; }
    case "CPI": { const v=parseNumber(a), result=byte(cpu.r.A-v); cpu.f.CY=cpu.r.A<v?1:0; cpu.f.AC=(cpu.r.A&15)<(v&15)?1:0;setSZP(result);break; }
    case "OUT": cpu.ports[ins.port]=cpu.r.A; if(ins.port===parseNumber($("dacPort").value)) addSample(cpu.r.A); break;
    case "IN": cpu.r.A=cpu.ports[ins.port];setSZP(cpu.r.A);break;
    case "JMP": next=ins.target;break;
    case "JNZ": if(!cpu.f.Z) next=ins.target;break;
    case "JZ": if(cpu.f.Z) next=ins.target;break;
    case "JC": if(cpu.f.CY) next=ins.target;break;
    case "JNC": if(!cpu.f.CY) next=ins.target;break;
    case "ADI": { const v=parseNumber(a),sum=cpu.r.A+v;cpu.f.CY=sum>255?1:0;cpu.f.AC=((cpu.r.A&15)+(v&15))>15?1:0;cpu.r.A=byte(sum);setSZP(cpu.r.A);break; }
    case "SUI": { const v=parseNumber(a),old=cpu.r.A;cpu.f.CY=old<v?1:0;cpu.f.AC=(old&15)<(v&15)?1:0;cpu.r.A=byte(old-v);setSZP(cpu.r.A);break; }
    case "ANI": case "ORI": case "XRI": { const v=parseNumber(a);cpu.r.A=byte(ins.op==="ANI"?(cpu.r.A&v):ins.op==="ORI"?(cpu.r.A|v):(cpu.r.A^v));cpu.f.CY=0;cpu.f.AC=ins.op==="ANI"?1:0;setSZP(cpu.r.A);break; }
  }
  cpu.PC=next; instructionCount++;
  updateDisplay();
  return !cpu.halted;
}
function updateMeasurements() {
  const panel = {
    max: $("maxVoltage"),
    min: $("minVoltage"),
    peak: $("peakToPeak"),
    average: $("averageVoltage")
  };

  if (samples.length === 0) {
    Object.values(panel).forEach(el => {
      if (el) el.textContent = "--";
    });
    return;
  }

  const voltages = samples.map(sample => sample.y);

  const max = Math.max(...voltages);
  const min = Math.min(...voltages);
  const average =
    voltages.reduce((sum, value) => sum + value, 0) / voltages.length;

  if (panel.max) panel.max.textContent = max.toFixed(3) + " V";
  if (panel.min) panel.min.textContent = min.toFixed(3) + " V";
  if (panel.peak) panel.peak.textContent = (max - min).toFixed(3) + " V";
  if (panel.average) panel.average.textContent = average.toFixed(3) + " V";

  const count = $("measurementSampleCount");
  if (count) count.textContent = samples.length;
}
function addSample(value) {
  const ref=parseFloat($("referenceVoltage").value);
  if(!Number.isFinite(ref)||ref<=0) throw new Error("Reference voltage must be greater than zero.");
  const voltage=(value/255)*ref;
  samples.push({x:samples.length,y:voltage,raw:value});
  chart.data.datasets[0].data=samples.map(s=>({x:s.x,y:s.y}));
  chart.update("none");
  $("sampleCount").textContent=samples.length;
  $("sampleSummary").textContent=`Latest DAC input: ${hex(value)} (${value}) → ${voltage.toFixed(3)} V`;
  updateMeasurements();
}

function updateDisplay() {
  const names=["A","B","C","D","E","H","L"];
  $("registerGrid").innerHTML=names.map(n=>`<div class="register"><span>${n}</span><strong>${hex(cpu.r[n])}</strong></div>`).join("")+
    `<div class="register"><span>SP</span><strong>${hex(cpu.SP,4)}</strong></div>`;
  $("flagsRow").innerHTML=Object.entries(cpu.f).map(([k,v])=>`<span class="flag ${v?"on":""}">${k}: ${v}</span>`).join("");
  $("instructionCount").textContent=instructionCount;
  $("pcValue").textContent=hex(cpu.PC,4);
  $("currentInstruction").textContent=lastInstruction;
  $("statusPill").textContent=cpu.halted?"Halted":running?"Running":"Ready";
}

function showMessage(message,type="info") { const el=$("messageBox");el.className=`message-box ${type}`;el.textContent=message; }
function resetSimulation(clearGraph=true) {
  stopRun();
  const start=parseNumber($("startAddress").value);
  if(start>65535) throw new Error("Start address must be between 0000H and FFFFH.");
  cpu=makeCPU(start); instructionCount=0;lastInstruction="Not started";
  if(clearGraph) { samples=[];chart.data.datasets[0].data=[];chart.update();$("sampleCount").textContent="0";$("sampleSummary").textContent="No DAC samples yet."; }
  updateDisplay();
}

function assembleCurrent() {
  const start=parseNumber($("startAddress").value);
  const result=assemble($("assemblyCode").value,start);
  program=result.instructions;labels=result.labels;
  assembledSnapshot = [$("assemblyCode").value, $("startAddress").value, $("dacPort").value, $("referenceVoltage").value].join("|");
  if(!program.length) throw new Error("The editor is empty.");
  $("listingBody").innerHTML=program.map(i=>`<tr><td>${hex(i.address,4)}</td><td>${escapeHTML(i.source)}</td><td>${i.size}</td></tr>`).join("");
  resetSimulation(true);
  showMessage(`Assembly successful: ${program.length} instruction lines, starting at ${hex(start,4)}.`, "success");
}

function escapeHTML(s) { return s.replace(/[&<>"']/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c])); }

function runProgram() {
  try {
    const currentSnapshot = [$("assemblyCode").value, $("startAddress").value, $("dacPort").value, $("referenceVoltage").value].join("|");
    if(!program.length || currentSnapshot !== assembledSnapshot) assembleCurrent();
    if(cpu.halted) resetSimulation(true);
    running=true;updateDisplay();showMessage("Executing program…","info");
    let count=0;
    const tick=()=>{
      if(!running) return;
      try {
        while(count<500 && !cpu.halted) { executeOne();count++; }
        if(cpu.halted) { stopRun();showMessage("Program halted successfully.","success");return; }
        if(count>=100000) { stopRun();showMessage("Execution limit reached (100,000 instructions). This may be an intentional infinite loop. Samples collected so far are displayed.","info");return; }
        timer=setTimeout(tick,0);
      } catch(e) { stopRun();showMessage(e.message,"error"); }
    };
    // Keep a total limit across animation batches.
    let total=0;
    const batch=()=>{
      if(!running)return;
      try {
        let n=0;
        while(n<500 && total<100000 && !cpu.halted) { executeOne();n++;total++; }
        if(cpu.halted) {stopRun();showMessage("Program halted successfully.","success");}
        else if(total>=100000) {stopRun();showMessage("Execution limit reached (100,000 instructions). The program may contain an intentional infinite loop. Samples collected so far are displayed.","info");}
        else timer=setTimeout(batch,0);
      } catch(e) {stopRun();showMessage(e.message,"error");}
    };
    batch();
  } catch(e) { showMessage(e.message,"error"); }
}
function stopRun() { running=false;if(timer)clearTimeout(timer);timer=null;if(cpu) updateDisplay(); }
function stepProgram() {
  try {
    const currentSnapshot = [$("assemblyCode").value, $("startAddress").value, $("dacPort").value, $("referenceVoltage").value].join("|");
    if(!program.length || currentSnapshot !== assembledSnapshot) assembleCurrent();
    if(cpu.halted) {showMessage("The processor is halted. Press Reset before stepping again.","info");return;}
    executeOne();
    showMessage(cpu.halted?"HLT executed. Processor halted.":"Executed one instruction.","success");
  } catch(e) { showMessage(e.message,"error"); }
}

function initChart() {
  const ctx=$("waveChart").getContext("2d");
  chart=new Chart(ctx,{
  type:"line",
  data:{
    datasets:[{
      label:"DAC output",
      data:[],
      borderColor:"#16845b",
      backgroundColor:"rgba(22,132,91,.10)",
      borderWidth:2,
      pointRadius:0,
      tension:0,
      stepped:"after",
      fill:false
    }]
  },
    options:{responsive:true,maintainAspectRatio:false,animation:false,parsing:false,scales:{x:{type:"linear",title:{display:true,text:"Sample index"},ticks:{color:"#64748b"},grid:{color:"#e8edf4"}},y:{beginAtZero:true,title:{display:true,text:"Output voltage (V)"},ticks:{color:"#64748b"},grid:{color:"#e8edf4"}}},plugins:{legend:{display:false}}}});
}
$("loadExampleBtn").addEventListener("click",()=>{$("assemblyCode").value=exampleCode;showMessage("Triangular waveform example loaded.","success");});
$("runBtn").addEventListener("click",runProgram);
$("stepBtn").addEventListener("click",stepProgram);
$("stopBtn").addEventListener("click",()=>{stopRun();showMessage("Execution stopped by user.","info");});
$("resetBtn").addEventListener("click",()=>{try{if(!program.length)assembleCurrent();else{resetSimulation(true);showMessage("Processor and waveform reset.","success");}}catch(e){showMessage(e.message,"error");}});
$("clearGraphBtn").addEventListener("click",()=>{samples=[];chart.data.datasets[0].data=[];chart.update();$("sampleCount").textContent="0";$("sampleSummary").textContent="No DAC samples yet.";});
initChart();
try { assembleCurrent(); } catch(e) { showMessage(e.message,"error"); }
