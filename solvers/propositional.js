function Proposition(tokens) {
	if(tokens.length==0) {
		this.error = "Cannot parse empty expression";
		return;
	}
	
	var symbols = {'p':1, 'q':1, 'r':1, 's':1, 't':1, 'U':1, 'V':1, 'w':1, 'x':1, 'y':1, 'z':1};
	var operators = {
		'and' : {'precedence':40, 'assoc':'left', 'op': (x,y)=>{return x&&y;}}, 
		'or'  : {'precedence':30, 'assoc':'left', 'op': (x,y)=>{return x||y;}}, 
		'imp' : {'precedence':20, 'assoc':'right', 'op': (x,y)=>{return !x || y;}},
		'eqv' : {'precedence':10, 'assoc':'left', 'op': (x,y)=>{return (!x||y)&&(!y||x)}},
		'nnd' : {'precedence':35, 'assoc':'left', 'op': (x,y)=>{return !(x&&y);}},
		'nor' : {'precedence':35, 'assoc':'left', 'op': (x,y)=>{return !(x||y);}},
		'xor' : {'precedence':35, 'assoc':'left', 'op': (x,y)=>{return (x&&!y)||y&&!x}}		
	};
	
	// Shunting Yard parser
	
	var output = [];
	var opque = [];
	
	for(var i=0;i<tokens.length;i++) {
		var token = tokens[i];
		if(token in symbols) {
			output.push(token);
			continue;
		}
		if(token=="not") {
			opque.push(token);
			continue;
		}		
		if(token in operators) {
			if(opque.length>0){							
				var lastop = opque[opque.length-1];				
				while(opque.length>0 && lastop!="left" && (operators[lastop].precedence>operators[token].precedence ||
					 (operators[lastop].precedence==operators[token].precedence && operators[token].assoc=="left") || lastop=="not")) {
					output.push(opque.pop());
					if(opque.length>0) {
						lastop = opque[opque.length-1];
					}
				} 						 				
			}			
			opque.push(token);			
			continue;
		}
		if(token=="left") {
			opque.push(token);
			continue;
		}
		if(token=="right") {
			var leftfound=false;
			while(!leftfound) {
				if(opque.length==0) {
					this.error = "Parenthesis mismatch";
					return;
				}
				var last = opque.pop();
				leftfound = (last=="left");
				if(!leftfound) {
					output.push(last);
				}
			}
			continue;
		}		
		
		if(opque.length==0) {
			this.error = `Unidentified token: ${tokens[i]}`;
			return;
		}
	}
	while(opque.length>0) {
		var last=opque.pop();
		if(last=="left") {
			this.error = "Parenthesis mismatch";
			return;
		}		
		output.push(last);
	}
	
	this.polish = [];
	for(var i=0;i<output.length;i++) {
		this.polish.push(output[i]);
	}
	
	console.log(this.polish);
	
	this.variables=[];
	
	for(var i=0;i<this.polish.length;i++) {
		if(this.polish[i] in symbols) {
			//this.variables[this.polish[i]]=false;
			this.variables.push(this.polish[i]);
		}
	}		
	this.variables.sort();
	var vardict = {};
	
	for(var i=0;i<this.variables.length;i++) {
		vardict[this.variables[i]]=false;
	}
	this.variables=vardict;
	
	console.log(this.variables);
	
	this.evaluate = function() {
		this.evaldbg={};
		var value = this.compute(this.polish.length-1);
		var keys= Object.keys(this.evaldbg);
		keys.sort((u,v)=>{if(u.length!=v.length) return u.length-v.length; return u<v?-1:1;});
		//console.log(keys);
		var dbg = [];
		for(var i=0;i<keys.length;i++) {
			dbg.push([keys[i],this.evaldbg[keys[i]]]);
		}
		this.evaldbg = dbg;
		return value;
	}
	
	this.evaldbg={};
	
	this.compute = function(ppos) {
		//console.log(ppos);
		var tk = this.polish[ppos];
		if(tk in symbols) {
			this.evaldbg[tk]=this.variables[tk];
			//console.log(tk);
			return [this.variables[tk],1,tk];
		}
		if(tk == "not") {			
			var c=this.compute(ppos-1);
			this.evaldbg[tokenToString("not")+c[2]]=!c[0];
			//console.log(tokenToString("not")+c[2]);
			return [!c[0],1+c[1],tokenToString("not")+c[2]];
		}
		if(tk in operators) {
			var right = this.compute(ppos-1);
			var left = this.compute(ppos-1-right[1]);			
			var txtr = right[2];
			//console.log(left);
			var txtl = left[2];			
			if(txtr.length>1) txtr="("+txtr+")";
			if(txtl.length>1) txtl="("+txtl+")";
				
			//console.log(txtl+tokenToString(tk)+txtr);
			this.evaldbg[txtl+tokenToString(tk)+txtr]=operators[tk].op(left[0],right[0]);
			return [operators[tk].op(left[0],right[0]),1+left[1]+right[1],txtl+tokenToString(tk)+txtr];
		}						
	}
}


function tokenToString(token) {	
	if(token== "left") return "("	
	if(token=="right") return ")";	
	if(token=="not") return "\u00AC"; 	
	if(token=="xor") return "\u2295";
	if(token=="and") return "\u2227";
	if(token== "or") return "\u2228";
	if(token=="imp") return "\u2192";
	if(token=="eqv") return "\u2194&#xFE0E;";
	if(token=="nnd") return "\u2191";
	if(token=="nor") return "\u2193";	
	if(/[a-zA-z]/.test(token)) return token;
}




