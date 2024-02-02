
;(function() {

let input = "#esolc##,di##,-##,2gra##,rahctup,1gra##,,,,bir##;)G60@;,A@A9,A@C<,A@D:,A@E7,A@BK";
// )@@
const debug = false;
// )@@
const lengthAttr = "length";
// Implement putchar/getchar to the terminal

const putchar = (c) => {
    let buffer = Buffer.alloc(1);
    buffer[0] = c;
    fs.writeSync(1, buffer, 0, 1);
    return c;
};

const getchar_sync = () => {
    let buffer = Buffer.alloc(1);
    if (fs.readSync(0, buffer, 0, 1))
        return buffer[0];
    return -1;
};

const getchar = () => {
    push(pos<input[lengthAttr] ? get_byte() : getchar_sync());
    return true; // indicate that no further waiting is necessary
};

const sym2str = (s) => chars2str(s[1][0]);  //debug
const chars2str = (s) => (s===NIL) ? "" : (String.fromCharCode(s[0])+chars2str(s[1]));  //debug

// )@@
// --------------------------------------------------------------

// VM

// build the symbol table

let pos = 0;
const get_byte = () => input[pos++].charCodeAt(0);
const get_code = () => { let x = get_byte()-35; return x<0 ? 57 : x; };
const get_int = (n) => { let x = get_code(); n *= 46; return x<46 ? n+x : get_int(n+x-46); };


const pop = () => { let x = stack[0]; stack = stack[1]; return x; };

const FALSE = [0,0,5]; TRUE = [0,0,5]; NIL = [0,0,5];

let symtbl = NIL;
let n = get_int(0);
while (n-- > 0) symtbl=[[0,[NIL,0,3],2],symtbl,0]; // symbols with empty names

accum = NIL;
n = 0;
while (1) {
  c = get_byte();
  if (c == 44) { symtbl=[[0,[accum,n,3],2],symtbl,0]; accum = NIL; n = 0; continue; }
  if (c == 59) break;
  accum = [c,accum,0];
  n++;
}

symtbl = [[0,[accum,n,3],2],symtbl,0];

const symbol_ref = (n) => list_tail(symtbl,n)[0];
const list_tail = (x,i) => i ? list_tail(x[1],i-1) : x;
const inst_tail = (x,i) => i ? inst_tail(x[2],i-1) : x;

// decode the instruction graph

let stack=0;
while(1){
    const x = get_code();
    let d = 0;
    n=x;
    op=-1;

    while((d=[0,1,6,1,0,1,5,1,0,1,10,1,0,1,0,1,6,2,0,1,3,1,0,1,1][++op])<=n) n-=d; // @@(replace "[0,1,6,1,0,1,5,1,0,1,10,1,0,1,0,1,6,2,0,1,3,1,0,1,1]" (list->host encoding/optimal/start "[" "," "]"))@@
    if (op<4) stack = [0,stack,0];
    if (op<24) n=op%2>0?get_int(n):n;

    if(op<20){ // jump call set get const
        i=op/4-1;
        i=i<0?0:i>>0;
        n=op%4/2<1?n:symbol_ref(n);
    }
    else if(op<22){ // const-proc
        n = [[n,0,pop()],0,1];
        i=3;
        if(!stack) break;
    }
    else if(op<24){ // skip
        stack = [inst_tail(stack[0], n), stack, 0];
        continue;
    }
    else if(op<25){ // if
        n=pop();
        i=4;
    }
    stack[0]=[i,n,stack[0]];
}


// )@@
const set_global = (x) => { symtbl[0][0] = x; symtbl = symtbl[1]; };

set_global([0,symtbl,1]); // primitive 0
set_global(FALSE);
set_global(TRUE);
set_global(NIL);

// RVM core

let pc = n[0][2];

stack = [0,0,[5,0,0]]; // primordial continuation (executes halt instr.)

const push = (x) => ((stack = [x,stack,0]), true);
// )@@
const is_rib = (x) => {
    if (x === undefined) console.log(stack);
    return x[lengthAttr];
};

const get_opnd = (o) => is_rib(o) ? o : list_tail(stack,o);
const get_cont = () => { let s = stack; while (!s[2]) s = s[1]; return s; };

const prim1 = (f) => () => push(f(pop()));
const prim2 = (f) => () => push(f(pop(),pop()));
const prim3 = (f) => () => push(f(pop(),pop(),pop()));

const primitives = [
  prim3((z, y, x) => [x, y, z]),                    //  @@(primitive (##rib a b c))@@
  prim1((x) => x),                                  //  @@(primitive (##id x))@@
  () => (pop(), true),                              //  @@(primitive (##arg1 x y))@@
  () => push([pop(),pop()][0]),                     //  @@(primitive (##arg2 x y))@@
  () => push([pop()[0],stack,1]),                   //  @@(primitive (##close rib))@@
  prim2((y, x) => x-y),                             //  @@(primitive (##- x y))@@
];

const run = () => {
  while (1) {
    let o = pc[1];
    switch (pc[0]) {
    case 5: // halt
        return;
    case 0: // jump/call
        o = get_opnd(o)[0];
        while(1) {
            if (debug) { console.log((pc[2]===0 ? "--- jump " : "--- call ") + show_opnd(o)); show_stack(); } //debug
            let c = o[0];

            if (is_rib(c)) {
                let c2 = [0,o,0];
                let s2 = c2;

                let nparams = c[0] >> 1;
                while (nparams--) s2 = [pop(),s2,0];

                if (pc[2]===0) {
                    // jump
                    let k = get_cont();
                    c2[0] = k[0];
                    c2[2] = k[2];
                } else {
                    // call
                    c2[0] = stack;
                    c2[2] = pc[2];
                }
                stack = s2;
            } else {
                o=primitives[c]();
                if (!o) return;
                if (is_rib(o)) continue;
                if (pc[2]===0) {
                    // jump
                    c = get_cont();
                    stack[1] = c[0];
                } else {
                    // call
                    c = pc;
                }
            }
            pc = c;
            break;
        }
        break;
    case 1: // set
        if (debug) { console.log("--- set " + show_opnd(o)); show_stack(); } //debug
        get_opnd(o)[0] = pop();
        break;
    case 2: // get
        if (debug) { console.log("--- get " + show_opnd(o)); show_stack(); } //debug
        push(get_opnd(o)[0]);
        break;
    case 3: // const
        if (debug) { console.log("--- const " + (is_rib(o) ? "" : ("int " + o))); show_stack(); } //debug
        push(o);
        break;
    case 4: // if
        if (debug) { console.log("--- if"); show_stack(); } //debug
        if (pop() !== FALSE) { pc = pc[1]; continue; }
        break;
    }
      pc = pc[2];
  }
};

  run(); // @@(feature (not js/web))@@
})();
