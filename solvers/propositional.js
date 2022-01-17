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

SemTableNode.prototype.clone = function() {
	var node = new SemTableNode(this.tag);
	node.id=this.id;
	node.formation=[this.formation[0],this.formation[1]];
	for(var i=0;i<this.children.length;i++) {
		node.children.push(this.children[i].clone());
	}
	return node;
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
	
	function appendNodesToLeaves(target,nodes,was_alpha=false) {
		//console.log("Called by",target.id,target.tag.toString());
		if(target.children.length==0) {
			for(var i=0;i<nodes.length;i++) {				
				var new_node = nodes[i].clone();
				target.children.push(new_node);
				
				if(new_node.id>0) {
					unsolved.push(new_node);
				}
				
				if(was_alpha) {
					if(new_node.children[0].id>0) {						
						unsolved.push(new_node.children[0]);
					}	
				}				
			}			
			return;
		}
		for(var i=0;i<target.children.length;i++)
			appendNodesToLeaves(target.children[i], nodes, was_alpha);
	}
	
	function getMaxDepth(target) {
		if(target.children.length==0) {
			return 1;
		}
		var d=0;
		for(var i=0;i<target.children.length;i++) {
			d=Math.max(d,getMaxDepth(target.children[i]));
		}
		return 1+d;
	}
	
	//console.log(root.toString());

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
				
				//console.log(nd1.formation);
				nd2.formation = ["x",-1];
				nd1.children.push(nd2);
												
				//for(var j=0;j<threads.length;j++) {
				//	threads[j].children.push(nd1);
				//}
				//threads=[nd2];
				//console.log("pushing to",node.id);		
				appendNodesToLeaves(node,[nd1],true);

				unsolved.splice(i,1);  i--;
				alphaCnt++;				
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
													
					//for(var j=0;j<threads.length;j++) {
						//threads[j].children.push(nd1);
						//threads[j].children.push(nd2);
					//}
					//threads=[nd1,nd2];
					appendNodesToLeaves(node,[nd1,nd2],false);

					unsolved.splice(i,1);  i--;
					betaCnt++;
				}			
				
			}
		}			
	}				
	
	//console.log(result);		
	
	var depth=getMaxDepth(result);
	
	var table = document.createElement("table");
	
	for(var i=0;i<2*depth;i++) {		
		table.appendChild(document.createElement("tr"));
	}	
	
	var node = result;	
	
	var td = document.createElement("td");
	td.innerHTML = node.tag.toString() + `&nbsp;&nbsp;&nbsp;<b>(${result.id})</b>`;
	td.innerHTML = `&nbsp;&nbsp;&nbsp;<b style="color:transparent">(${result.id})</b>` + td.innerHTML;
	table.children[0].appendChild(td);	
	table.children[1].appendChild(document.createElement("td"));
		
	var stack = [];
	for(var i=0;i<result.children.length;i++) stack.push([result.children[i],1,0,1,0]);
	
	var max_magnitude = 1;
	while(stack.length>0) {
		var el = stack.shift();
		var nd=el[0];
		var row = el[1];
		var magnitude = el[2];
		var mgmax = el[3];
		var initialm = el[4];
		
		max_magnitude = Math.max(max_magnitude,mgmax);
		
		//console.log(mgmax);
		
		while(table.children[2*row].children.length!=mgmax) {
			table.children[2*row].appendChild(document.createElement("td"));
			table.children[2*row+1].appendChild(document.createElement("td"));
		}			
		
		
		var td = table.children[2*row].children[magnitude];
		td.innerHTML = nd.tag.toString();			
		if(nd.id!=0) {
			td.innerHTML += `&nbsp;&nbsp;&nbsp;<b>(${nd.id})</b>`;
			td.innerHTML = `&nbsp;&nbsp;&nbsp;<b style="color:transparent">(${nd.id})</b>`+td.innerHTML;
		}					
		
		var td = table.children[2*row-1].children[initialm];
		var f0 = nd.formation[0];
		var f1 = nd.formation[1];
		
		if(f0!="x"){				
			td.innerHTML = `<i>${f0}(${f1})</i>`;
			if(f0=='a') {
				td.innerHTML = `<i style="color:transparent">${f0}(${f1})</i>&nbsp;|&nbsp;<i>${f0}(${f1})</i>`;
			}
			else if(f0=='b') {
				td.innerHTML = `<i style="color:transparent">${f0}(${f1})</i>&nbsp;/&nbsp;   &nbsp;\\&nbsp;<i>${f0}(${f1})</i>`;
			}
		}
		else {
			td.innerHTML="|";
		}		
		
		for(var i=0;i<nd.children.length;i++) {
			stack.push([nd.children[i],row+1,nd.children.length*magnitude+i,mgmax*nd.children.length, magnitude]);
		}						
	}
	
	var tr = document.createElement("tr");
	for(var i=0;i<max_magnitude;i++) {
		tr.appendChild(document.createElement("td"));
	}
	table.appendChild(tr);
	
	var colscnt = max_magnitude;;
	
	for(var i=0;i<table.children.length;i++) {
		var row = table.children[i];
		var cnt = Math.floor(colscnt/row.children.length);		
		for(var j=0;j<row.children.length;j++) {			
			row.children[j].colSpan=cnt;
			row.children[j].style.width=(100/colscnt)+"%";
			row.children[j].style.textAlign="center";
		}
	}
	
	//console.log(colscnt);
	
	//console.log(depth);
	
	var litcolors = {};
	var clindex = 0;
	var colors = ['#880000', '#008800', '#000088', '#880088', '#008888', '#888800'];
	
	var open_b = 0;
	var closed_b = 0;
	
	for(var i=0;i<colscnt;i++) {
		var rid = 2*(depth-1);
		var literals = [];
		var j=i;
		while(rid>=0) {
			var row = table.children[rid];			
			if(j>=row.children.length) j=Math.floor(j/2);						
			var expr=row.children[j].innerHTML;
			if(expr.length==1) {
				if(expr in symbols) {
					literals.push([expr,1,row.children[j]]);
				}
			}
			else if(expr.length==2) {
				if(expr[0]==tokenToString("not") && (expr[1] in symbols)) {
					literals.push([expr[1],0,row.children[j]]);
				}
			}			
			rid-=2;
		}	
		//console.log(literals);
		
		var solved={};		
		for(var j=0;j<literals.length-1;j++) {
			if(!solved[literals[j][0]]){
				for(var k=j+1;k<literals.length;k++) {
					if(literals[j][0]==literals[k][0] && literals[j][1]!=literals[k][1]) {
						solved[literals[j][0]]=1;
						
						var lit = literals[j][0];
						if(!(lit in litcolors)) {
							litcolors[lit]=colors[clindex++];
						}			
						
						literals[j][2].className="literal";
						literals[k][2].className="literal";
						
						literals[j][2].style.color=litcolors[lit];
						literals[k][2].style.color=litcolors[lit];																
						
						//literals[j][2].style.border="1px solid "+litcolors[lit];
						//literals[k][2].style.border="1px solid "+litcolors[lit];											
					}
				}
			}
		}
		
		if(Object.keys(solved).length>0) {
			rid = 2*depth;
			var j=i;
			while(table.children[rid].children[i].innerHTML=="") {											
				rid--;
			}			
			table.children[rid+1].children[i].innerHTML="|";
			table.children[rid+2].children[i].innerHTML="<span style='font-size:30px;'>&#119109;</span>";
			closed_b++;
		}
		else {		
			rid = 2*depth;
			var j=i;
			while(table.children[rid].children[i].innerHTML=="") {											
				rid--;
			}			
			table.children[rid+1].children[i].innerHTML="|";
			table.children[rid+2].children[i].innerHTML="<span style='font-size:18px;'>&#8857;</span>";			
			open_b++;
		}			
	}
	
	
	//console.log(table);
	
	table.className="semantic";
	
	var center=document.createElement("center");
	center.appendChild(table);
	
	//console.log(depth);	
	
	this.ui = center;
	this.open_branches = open_b;
	this.closed_branches = closed_b;
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




