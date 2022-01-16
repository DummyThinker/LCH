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

function Proposition(tokens) {
	if(tokens.length==0) {
		this.error = "Cannot parse empty expression";
		return;
	}	
	
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
				while(opque.length>0 && lastop!="left" && ((lastop!="not" && (operators[lastop].precedence>operators[token].precedence ||
					 (operators[lastop].precedence==operators[token].precedence && operators[token].assoc=="left"))) || lastop=="not")) {
					output.push(opque.pop());
					if(opque.length>0) {
						lastop = opque[opque.length-1];
					}
					while(opque.length>0 && lastop=="not") {
						output.push(opque.pop());
						if(opque.length>0) lastop = opque[opque.length-1];
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
	
	//console.log(this.polish);
	
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
	
	//console.log(this.variables);
	
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

function PropositionalNode(token,left=null,right=null) {
	this.token=token;
	this.left=left;
	this.right=right;	
}

PropositionalNode.prototype.toString = function() {
	if(this.token in symbols){
		return this.token;
	}
	if(this.token == "not") {
		var left = this.left.toString();
		if(left.length>1) left="("+left+")";
		return tokenToString("not")+left;
	}
	var left=this.left.toString();
	var right=this.right.toString();
	if(left.length>1) left="("+left+")";
	if(right.length>1) right="("+right+")";
	return left+tokenToString(this.token)+right;
}

PropositionalNode.prototype.isLiteral = function() {
	return (this.token in symbols) || (this.token=="not" && (this.left.token in symbols));
}

PropositionalNode.prototype.negate = function() {
	if(this.token!="not")
		return new PropositionalNode("not", this);
	return this.left;
}

function propagateNegation(pNode, applyToChildren=false) {
	
	//console.log("formF",JSON.stringify(pNode));
	
	if(pNode.token!="not") return pNode;
	if(pNode.left.token in symbols) return pNode;	
	
	var target = pNode.left;
	if(target.token=="or") {
		pNode.token="and";
		var left = target.left;
		var right = target.right;
		left = new PropositionalNode("not",left,null);
		right = new PropositionalNode("not",right,null);		
		pNode.left=left;
		pNode.right=right;
		
		if(applyToChildren) {
			pNode.left = propagateNegation(pNode.left,true);
			pNode.right = propagateNegation(pNode.right,true);
		}
		return pNode;
	}
	
	if(target.token=="and") {
		pNode.token="or";
		var left = target.left;
		var right = target.right;
		left = new PropositionalNode("not",left,null);
		right = new PropositionalNode("not",right,null);
		
		if(applyToChildren) {
			//console.log(left);
			left = propagateNegation(left,true);
			//console.log(left);
			right = propagateNegation(right,true);
		}
		
		pNode.left=left;
		pNode.right=right;
		
		return pNode;
	}
	
	if(target.token=="imp") {
		pNode.token="and";
		var left = target.left;
		var right = target.right;
		right = new PropositionalNode("not",right,null);
		pNode.left=left;
		pNode.right=right;
		
		if(applyToChildren) {
			pNode.left = propagateNegation(pNode.left,true);
			pNode.right = propagateNegation(pNode.right,true);
		}
		return pNode;
	}
	
	if(target.token=="eqv") {
		pNode.token="eqv";
		var left = target.left;
		var right = target.right;
		left = new PropositionalNode("not",left,null);
		right = new PropositionalNode("not",right,null);
		pNode.left=left;
		pNode.right=right;	
		
		if(applyToChildren) {
			pNode.left = propagateNegation(pNode.left,true);
			pNode.right = propagateNegation(pNode.right,true);
		}
		return pNode;
	}
	
	if(target.token=="xor") {
		pNode.token="xor";
		var left = target.left;
		var right = target.right;
		right = new PropositionalNode("not",right,null);
		pNode.left=left;
		pNode.right=right;
		
		if(applyToChildren) {
			pNode.left = propagateNegation(pNode.left,true);
			pNode.right = propagateNegation(pNode.right,true);
		}
		return pNode;
	}
	
	if(target.token=="nnd") {
		pNode.token="nor";
		var left = target.left;
		var right = target.right;
		left = new PropositionalNode("not",left,null);
		right = new PropositionalNode("not",right,null);
		pNode.left=left;
		pNode.right=right;
		
		if(applyToChildren) {
			pNode.left = propagateNegation(pNode.left,true);
			pNode.right = propagateNegation(pNode.right,true);
		}
		return pNode;
	}
	
	if(target.token=="nor") {
		pNode.token="nnd";
		var left = target.left;
		var right = target.right;
		left = new PropositionalNode("not",left,null);
		right = new PropositionalNode("not",right,null);
		pNode.left=left;
		pNode.right=right;
		
		if(applyToChildren) {
			pNode.left = propagateNegation(pNode.left,true);
			pNode.right = propagateNegation(pNode.right,true);
		}
		return pNode;
	}
	
	if(target.token=="not") {		
		pNode = target.left;
		
		if(applyToChildren) {
			pNode = propagateNegation(pNode,true);
		}		
		return pNode;
	}
}

function PropositionalTree(proposition) {
	this.root = createTree(proposition,proposition.polish.length-1)[0];
		
	function createTree(prop,ppos) {
		var tk = prop.polish[ppos];
		if(tk in symbols) {
			return [new PropositionalNode(tk),1];
		}
		if(tk == "not") {			
			var c=createTree(prop, ppos-1);			
			return [new PropositionalNode(tk,c[0]),1+c[1]];
		}
		if(tk in operators) {
			var right = createTree(prop, ppos-1);
			var left = createTree(prop, ppos-1-right[1]);
						
			return [new PropositionalNode(tk,left[0],right[0]),1+left[1]+right[1]];
		}
	}
}

function SemTableNode(tag) {
	this.tag = tag;
	this.id = 0; // 0 = literal, 1, 2, ... = composed formulae, -1 = undefined
	
	this.formation = ["x", -1]; // ["a(lpha)", 1], ["b(eta)", 2] etc...
	
	this.children = [];
}

function decompose(root) {
	if(root.token=="and") {
		return ["a",root.left,root.right];
	}
	if(root.token=="or") {
		return ["b",root.left,root.right];		
	}
	if(root.token=="imp") {
		return ["b", root.left.negate(), root.right];
	}
	if(root.token=="not") {
		root = root.left;
		if(root.token=="and") {
			return ["b",root.left.negate(),root.right.negate()];
		}
		if(root.token=="or") {
			return ["a",root.left.negate(),root.right.negate()];
		}
		if(root.token=="imp") {
			return ["a", root.left, root.right.negate()];
		}
	}
	return [];
}

function createSemanticTable(root) {
	console.log(root.toString());

	var id=2;
	var result = new SemTableNode(root);	
	result.id=1;
	var unsolved = [result];
	var threads = [result];	
	
	var alphaCnt=1;
	var betaCnt=0;
	while(alphaCnt+betaCnt>0 && unsolved.length>0) {
		alphaCnt=betaCnt=0;
		
		for(var i=0;i<unsolved.length;i++) {
			var node = unsolved[i];
			//console.log("node=",node);
			var dec = decompose(node.tag);
			//console.log(dec);
			if(dec[0]=='a'){							
				var f1 = dec[1];
				var f2 = dec[2];
				
				var nd1  =new SemTableNode(f1);
				if(f1.isLiteral()) nd1.id=0; else { nd1.id = id; id++; }
				
				var nd2  =new SemTableNode(f2);
				if(f2.isLiteral()) nd2.id=0; else { nd2.id = id; id++; }
				
				nd1.formation = ["a",node.id];
				
				console.log(nd1.formation);
				nd2.formation = ["x",-1];
				nd1.children.push(nd2);
												
				for(var j=0;j<threads.length;j++) {
					threads[j].children.push(nd1);
				}
				threads=[nd2];

				unsolved.splice(i,1);  i--;
				alphaCnt++;
				
				if(!f1.isLiteral()) {
					unsolved.push(nd1);
				}
				if(!f2.isLiteral()) {
					unsolved.push(nd2);
				}
			}
		}				
		if(alphaCnt==0) {
			// solve beta
			for(var i=0;i<unsolved.length;i++) {
				var node = unsolved[i];
				var dec = decompose(node.tag);
				
				if(dec[0]=='b'){							
					var f1 = dec[1];
					var f2 = dec[2];
					
					var nd1  =new SemTableNode(f1);
					if(f1.isLiteral()) nd1.id=0; else { nd1.id = id; id++; }
					
					var nd2  =new SemTableNode(f2);
					if(f2.isLiteral()) nd2.id=0; else { nd2.id = id; id++; }
					
					nd1.formation = ["b",node.id];
					nd2.formation = ["b",node.id];
					
					console.log(nd1.formation);					
													
					for(var j=0;j<threads.length;j++) {
						threads[j].children.push(nd1);
						threads[j].children.push(nd2);
					}
					threads=[nd1,nd2];

					unsolved.splice(i,1);  i--;
					alphaCnt++;
					
					if(!f1.isLiteral()) {
						unsolved.push(nd1);
					}
					if(!f2.isLiteral()) {
						unsolved.push(nd2);
					}
				}			
				
			}
		}			
	}				
	
	console.log(result);	
		
	
	var depth=1;
	
	var node = result;
	while(node.children.length>0){
		node = node.children[0];
		depth++;
	}
	depth++;
	
	
	var table = document.createElement("table");
	
	for(var i=0;i<2*depth;i++) {		
		table.appendChild(document.createElement("tr"));
	}	
	
	
	var threads=1;
	var node = result;
	var depth=1;
	
	var td = document.createElement("td");
	td.innerHTML = node.tag.toString() + `&nbsp;&nbsp;&nbsp;<b>(${result.id})</b>`;
	td.innerHTML = `&nbsp;&nbsp;&nbsp;<b style="color:transparent">(${result.id})</b>` + td.innerHTML;
	table.children[0].appendChild(td);	
	
	
	while(node.children.length>0) {				
		for(var i=0;i<threads;i++) {
			var td = document.createElement("td");
			td.innerHTML = node.children[0].tag.toString();			
			if(node.children[0].id!=0) {
				td.innerHTML += `&nbsp;&nbsp;&nbsp;<b>(${node.children[0].id})</b>`;
				td.innerHTML = `&nbsp;&nbsp;&nbsp;<b style="color:transparent">(${node.children[0].id})</b>`+td.innerHTML;
			}			
			table.children[2*depth].appendChild(td);
			
			
			var td = document.createElement("td");
			var f0 = node.children[0].formation[0];
			var f1 = node.children[0].formation[1];
			
			if(f0!="x"){				
				td.innerHTML = `<i>${f0}(${f1})</i>`;
				if(f0=='a') {
					td.innerHTML = `<i style="color:transparent">${f0}(${f1})</i>&nbsp;|&nbsp;<i>${f0}(${f1})</i>`;
				}
				else if(f0=='b') {
					td.innerHTML = `<i style="color:transparent">${f0}(${f1})</i>/&nbsp;   &nbsp;\\<i>${f0}(${f1})</i>`;
				}
			}
			else {
				td.innerHTML="|";
			}
			table.children[2*depth-1].appendChild(td);
			
			if(node.children.length==2) {
				var td = document.createElement("td");
				td.innerHTML = node.children[1].tag.toString();
				if(node.children[1].id!=0) {
					td.innerHTML += `&nbsp;&nbsp;&nbsp;<b>(${node.children[1].id})</b>`;
					td.innerHTML = `&nbsp;&nbsp;&nbsp;<b style="color:transparent">(${node.children[1].id})</b>`+td.innerHTML;
				}				
				table.children[2*depth].appendChild(td);
			}
		}
		threads*=node.children.length;
		
		node = node.children[0];
		depth++;
	}
	
	for(var i=0;i<table.children.length;i++) {
		var row = table.children[i];
		var cnt = depth/row.children.length;
		for(var j=0;j<row.children.length;j++) {			
			row.children[j].colSpan=cnt;
			row.children[j].style.textAlign="center";
		}
	}
	
	
	
	console.log(table);
	
	var center=document.createElement("center");
	center.appendChild(table);
	
	console.log(depth);
	
	return center;		
}


function tokenToString(token) {	
	if(token== "left") return "(";
	if(token=="right") return ")";	
	if(token=="not") return "\u00AC"; 	
	if(token=="xor") return "\u2295";
	if(token=="and") return "\u2227";
	if(token== "or") return "\u2228";
	if(token=="imp") return "\u2192";
	if(token=="eqv") return "\u2194";
	if(token=="nnd") return "\u2191";
	if(token=="nor") return "\u2193";	
	if(/[a-zA-z]/.test(token)) return token;
}




