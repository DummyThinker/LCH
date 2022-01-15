function Minterm(argscnt, id) {
	this.argscnt = argscnt;
	this.id = id;
	
	this.name="m<sub>"+id+"</sub>";
	
	this.explicitForm = "";
	
	this.bits = getBits(id,argscnt);	
	for(var i=0;i<argscnt;i++) {
		this.explicitForm+="x";
		if(this.bits[i]==0) {
			this.explicitForm+="&#773;";
		}
		this.explicitForm+="<sub>"+i+"</sub>";
	}		
}

const subdigit = ["\u2080", "\u2081", "\u2082", "\u2083", "\u2084", "\u2085", "\u2086", "\u2087", "\u2088", "\u2089"];
function sub(n) {
	if(n==0) return subdigit[0];//String.fromCharCode(0x2080);
	var res="";
	while(n>0) {		
		res = subdigit[n%10]+res;//String.fromCharCode(0x2080 + n%10)+res;
		n=Math.floor(n/10);
	}	
	return res;
}

function TableFindGroups(rowscnt,colscnt,matrix,rowsdim,colsdim) {
	var result= [];
	for(var i=0;i<rowscnt;i++) {
		for(var j=0;j<colscnt;j++) {
			var ok=true;
			var mintermslist = []
			for(var x=0;x<rowsdim && ok;x++) {
				for(var y=0;y<colsdim && ok;y++) {
					if(matrix[(i+x)%rowscnt][(j+y)%colscnt]<0) ok=false;					
					mintermslist.push(matrix[(i+x)%rowscnt][(j+y)%colscnt]);
				}
			}
			
			if(ok) {
				mintermslist.sort(function(a,b){return a-b;});
				result.push({"x":i,"y":j,"rows":rowsdim,"cols":colsdim,"minterms":mintermslist});
			}
		}
	}
	
	var to_delete = [];
	for(var i=0;i<result.length-1;i++) {		
		for(var j=i+1;j<result.length;j++) {
			if(JSON.stringify(result[i].minterms)==JSON.stringify(result[j].minterms)) {				
				if(result[i].x<result[j].x || (result[i].x==result[j].x && result[i].y<result[j].y)) {
					var found = to_delete.find(element=>element==j);
					if(typeof(found)==="undefined") to_delete.push(j);
				}
				else {
					var found = to_delete.find(element=>element==i);
					if(typeof(found)==="undefined") to_delete.push(i);
				}
			}						
		}
	}
	
	to_delete.sort(function(a,b){return a-b;});
	var deleted=0;
	for(var i=0;i<to_delete.length;i++) {
		result.splice(to_delete[i]-deleted,1);
		deleted++;
	}
	return result;
}

function hasSubArray(master, sub) {
	var ok=true;
	for(var i=0;i<sub.length && ok;i++) {
		if(!master.includes(sub[i])) ok=false;
	}
	return ok;
    //return sub.every((i => v => i = master.indexOf(v, i) + 1)(0));
}

function Maxterm(argscnt,mintermids, id=0) {
	var self = this;
	
	self.argscnt = argscnt;
	self.mintermids = mintermids;
	self.id=id;	

	self.conjunction = []; // [ [argument_x_id, isNotNegated ], ... ]
	
	xs = [];
	for(var k=0;k<self.argscnt;k++) xs.push(0);
	for(var j=0;j<self.mintermids.length;j++) {		
		var bits = new getBits(self.mintermids[j],self.argscnt);				
		for(var k=0;k<self.argscnt;k++) xs[k]+=bits[k];
	}			
	
	for(var k=0;k<self.argscnt;k++) {
		if(xs[k]==self.mintermids.length) {
			self.conjunction.push([k, 1]);
		}
		else if(xs[k]==0) {			
			self.conjunction.push([k, 0]);
		}
	}			
	
	this.name = "max"+sub(id);	
	
	this.explicitForm = function() {
		var result="";		
		
		for(var i=0;i<self.conjunction.length;i++) {			
			result+="x";
			if(self.conjunction[i][1]==0) {
				result+="&#773;";
			}
			result+=sub(self.conjunction[i][0]+1);
		}		
		
		return result;
	}
	
	
	
	self.evaluate = function(x_args) {
		for(var i=0;i<self.conjunction.length;i++) {
			var term  = self.conjunction[i];
			if(x_args[term[0]] != term[1]) 
				return false;
		}
		return true;
	}			
}

Maxterm.prototype.toString = function(depth, opts) {
    return `max${sub(self.id)}`;
}

function BooleanFunction(argscnt) {
	var self=this;
	self.argscnt = argscnt;
	self.maxterms = [];
	
	self.evaluate = function(x_args) {
		for(var i=0;i<self.maxterms.length;i++) {
			if(self.maxterms[i].evaluate(x_args)) {
				return true;
			}
		}
		return false;
	}		
	
	self.getSupport = function() {
		var support = [];
		for(var x=0;x<Math.pow(2,self.argscnt);x++) {
			var xlst = getBits(x,self.argscnt);
			if(self.evaluate(xlst)) {
				support.push(x);
			}
		}
		return support;
	}
}

function findMaxtermsCase23(uncovered, maxterms) {
	var result = [];
	var n = Math.pow(2,maxterms.length);
	for(var i=1;i<n;i++){
		var bits = getBits(i,maxterms.length);
		
		var built = {};
		var candidate = [];
		for(var j=0;j<maxterms.length;j++) {
			if(bits[j]==1) {
				for(var k=0;k<maxterms[j].length;k++) {
					built[maxterms[j][k]]=1;					
				}
				candidate.push(j);
			}
		}
				
		var allin=true;//(Object.keys(built).length==uncovered.length);
		for(var j=0;j<uncovered.length && allin;j++) {
			allin = (built[uncovered[j]]==1);
		}		
		if(allin) {
			if(result.length==0)
				result.push(candidate);
			else if(result[0].length>candidate.length) {
					result = [candidate];					
				}
			else if(result[0].length==candidate.length) {
				result.push(candidate)
			}			
		}
	}	
	
	return result;
}

// 1, 3,4, 6,7,8,9 11, 12 ,13
function GroupsRemoveContained(groups) {
	var to_delete=[];
	
	for(var i=0;i<groups.length-1;i++) {		
		for(var j=i+1;j<groups.length;j++) {
			if(hasSubArray(groups[i].minterms,groups[j].minterms)) {
				var found = to_delete.find(element=>element==j);
				if(typeof(found)==="undefined") to_delete.push(j);				
				//console.log(groups[i].minterms,groups[j].minterms);
			}
			else if(hasSubArray(groups[j].minterms,groups[i].minterms)) {
				var found = to_delete.find(element=>element==i);
				if(typeof(found)==="undefined") to_delete.push(i);
				//console.log(groups[j].minterms,groups[i].minterms);
			}
		}
	}	
	
	to_delete.sort(function(a,b){return a-b;});	
	var deleted=0;
	for(var i=0;i<to_delete.length;i++) {
		groups.splice(to_delete[i]-deleted,1);		
		deleted++;
	}	
}

function VeitchTable(argscnt, minterms) {
	var self=this;
	this.tablesizes = {
		2: [2,2],
		3: [2,4],
		4: [4,4]
	};
	this.mintermspos = { // pos[minterm_id] = [row,col]
		2: [ [0,0], [0,1], [1,0], [1,1]],
		3: [ [0,0], [0,1], [0,3], [0,2], [1,0], [1,1], [1,3], [1,2]],
		4: [ [0,0], [0,1], [0,3], [0,2], [1,0], [1,1], [1,3], [1,2], [3,0], [3,1], [3,3], [3,2], [2,0], [2,1], [2,3], [2,2]]
	};	
	
	this.argscnt = parseInt(argscnt);
	
	this.rowscnt = this.tablesizes[this.argscnt][0];
	this.colscnt = this.tablesizes[this.argscnt][1];	
	
	var table = Array(this.rowscnt);
	for(var i=0;i<this.rowscnt;i++) {
		table[i]=Array(this.colscnt);
	}
	for(var i=0;i<this.rowscnt;i++)
		for(var j=0;j<this.colscnt;j++) {
			table[i][j]=-1;
		}
		
	for(var i=0;i<minterms.length;i++) {
		var mid = minterms[i].id;
		var pos = this.mintermspos[this.argscnt][mid];
		table[pos[0]][pos[1]]=mid;
	}	
	
	this.groups = [];
	if(this.argscnt>=2) {
		this.groups = this.groups.concat(
			TableFindGroups(this.rowscnt,this.colscnt,table,1,1),
			TableFindGroups(this.rowscnt,this.colscnt,table,1,2),
			TableFindGroups(this.rowscnt,this.colscnt,table,2,1),
			TableFindGroups(this.rowscnt,this.colscnt,table,2,2)
			);		
	}
	if(argscnt>=3) {
		this.groups = this.groups.concat(
			TableFindGroups(this.rowscnt,this.colscnt,table,1,4),
			TableFindGroups(this.rowscnt,this.colscnt,table,2,4)
			);
	}
	if(argscnt==4) {
		this.groups = this.groups.concat(
			TableFindGroups(this.rowscnt,this.colscnt,table,4,1),
			TableFindGroups(this.rowscnt,this.colscnt,table,4,2),
			TableFindGroups(this.rowscnt,this.colscnt,table,4,4)
			);
	}
	
	GroupsRemoveContained(this.groups);
	
	//console.log(this.groups);	
    
    this.getMaxterms = function() {
        var result=[];
        for(var i=0;i<self.groups.length;i++) {
            result.push(self.groups[i].minterms);
        }
        return result;
    }
	
	this.getMaxtermsList = function() {
		var result="";				
		for(var i=0;i<self.groups.length;i++) {								
			if(i>0) result+="<br/>";
			result+="max<sub>"+(i+1)+"</sub> = ";
			xs = [];
			for(var k=0;k<self.argscnt;k++) xs.push(0);
			for(var j=0;j<self.groups[i].minterms.length;j++) {
				if(j>0) result+="\u2228";
				result+="m<sub>"+self.groups[i].minterms[j]+"</sub>";													
				var bits = new getBits(self.groups[i].minterms[j],self.argscnt);				
				for(var k=0;k<self.argscnt;k++) xs[k]+=bits[k];
			}			
			result+=" = ";
			for(var k=0;k<self.argscnt;k++) {
				if(xs[k]==self.groups[i].minterms.length) {
					result+="x"+sub(k+1);	
				}
				else if(xs[k]==0) {
					result+="x&#773;"+sub(k+1);
				}
			}			
		}				
		return result;
	}	
	
	this.drawToContext = function(ctx,width,height,cellsize, type="V") {
		var tb_left = (width - cellsize*(self.colscnt-1))/2;
		var tb_top = (height - cellsize*(self.rowscnt-1))/2;		
		
		var fontsize = cellsize*2/5;
		
		//self.ctxText(ctx,"x\u{0305}\u{2080}\u{2081}\u{2082}\u{2083}\u{2084}\u{2085}\u{2086}\u{2087}\u{2088}\u{2089}",0,50,fontsize);
		
		if(self.argscnt==2) {
			self.ctxLine(ctx,tb_left-cellsize,tb_top,tb_left+2*cellsize,tb_top);
			self.ctxLine(ctx,tb_left-cellsize,tb_top+cellsize,tb_left+2*cellsize,tb_top+cellsize);
			self.ctxLine(ctx,tb_left-cellsize,tb_top+2*cellsize,tb_left+2*cellsize,tb_top+2*cellsize);
			
			self.ctxLine(ctx,tb_left,tb_top-cellsize,tb_left,tb_top+2*cellsize);
			self.ctxLine(ctx,tb_left+cellsize,tb_top-cellsize,tb_left+cellsize,tb_top+2*cellsize);			
			self.ctxLine(ctx,tb_left+2*cellsize,tb_top-cellsize,tb_left+2*cellsize,tb_top+2*cellsize);			
						
			if(type=="V") {
				self.ctxText(ctx,"x\u{0305}\u{2081}",tb_left-3*cellsize/4, tb_top+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"x\u{2081}",tb_left-3*cellsize/4, tb_top+2*cellsize-cellsize/4,fontsize);
				
				self.ctxText(ctx,"x\u{0305}\u{2082}",tb_left+cellsize-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"x\u{2082}",tb_left+cellsize*2-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);			
			}
			else if(type=="K") {				
				self.ctxText(ctx,"00",tb_left-3*cellsize/4, tb_top+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"01",tb_left-3*cellsize/4, tb_top+2*cellsize-cellsize/4,fontsize);
				
				self.ctxText(ctx,"00",tb_left+cellsize-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"01",tb_left+cellsize*2-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);			
				
				self.ctxLine(ctx,tb_left,tb_top,tb_left-cellsize,tb_top-cellsize);
				self.ctxText(ctx,"x\u{2081}",tb_left-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize*3/4);
				self.ctxText(ctx,"x\u{2082}",tb_left-cellsize+cellsize-3*cellsize/8, tb_top-cellsize/2,fontsize*3/4);
			}
		}
		else if(self.argscnt==3) {
			self.ctxLine(ctx, tb_left-cellsize, tb_top,          tb_left+4*cellsize, tb_top);
			self.ctxLine(ctx, tb_left-cellsize, tb_top+cellsize, tb_left+4*cellsize, tb_top+cellsize);
			self.ctxLine(ctx, tb_left-cellsize, tb_top+2*cellsize, tb_left+4*cellsize, tb_top+2*cellsize);			
						
			if(type=="V") {
				self.ctxLine(ctx, tb_left, tb_top-cellsize, tb_left, tb_top+2*cellsize);
				self.ctxLine(ctx, tb_left+2*cellsize, tb_top-cellsize, tb_left+2*cellsize, tb_top+2*cellsize);
				
				self.ctxLine(ctx, tb_left+cellsize, tb_top, tb_left+cellsize, tb_top+3*cellsize);
				self.ctxLine(ctx, tb_left+3*cellsize, tb_top, tb_left+3*cellsize, tb_top+3*cellsize);
				
				self.ctxLine(ctx, tb_left+4*cellsize, tb_top-cellsize, tb_left+4*cellsize, tb_top+2*cellsize);
				
				self.ctxText(ctx,"x\u{0305}\u{2081}",tb_left-3*cellsize/4, tb_top+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"x\u{2081}",tb_left-3*cellsize/4, tb_top+2*cellsize-cellsize/4,fontsize);
				
				self.ctxText(ctx,"x\u{0305}\u{2082}",tb_left+cellsize*3/2-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"x\u{2082}",tb_left+cellsize*7/2-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				
				self.ctxText(ctx,"x\u{0305}\u{2083}",tb_left+cellsize-3*cellsize/4, tb_top+2*cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"x\u{2083}",tb_left+cellsize*5/2-3*cellsize/4, tb_top+2*cellsize+cellsize-cellsize/4,fontsize);			
				self.ctxText(ctx,"x\u{0305}\u{2083}",tb_left+cellsize*4-3*cellsize/4, tb_top+2*cellsize+cellsize-cellsize/4,fontsize);	
			}			
			else if(type=="K") {
				self.ctxLine(ctx, tb_left, tb_top-cellsize, tb_left, tb_top+2*cellsize);
				self.ctxLine(ctx, tb_left+2*cellsize, tb_top-cellsize, tb_left+2*cellsize, tb_top+2*cellsize);
				
				self.ctxLine(ctx, tb_left+cellsize, tb_top-cellsize, tb_left+cellsize, tb_top+2*cellsize);
				self.ctxLine(ctx, tb_left+3*cellsize, tb_top-cellsize, tb_left+3*cellsize, tb_top+2*cellsize);
				
				self.ctxLine(ctx, tb_left+4*cellsize, tb_top-cellsize, tb_left+4*cellsize, tb_top+2*cellsize);
				
				self.ctxText(ctx,"00",tb_left-3*cellsize/4, tb_top+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"01",tb_left-3*cellsize/4, tb_top+2*cellsize-cellsize/4,fontsize);
				
				self.ctxText(ctx,"00",tb_left+cellsize-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"01",tb_left+2*cellsize-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"11",tb_left+3*cellsize-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"10",tb_left+4*cellsize-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				
				self.ctxLine(ctx,tb_left,tb_top,tb_left-cellsize,tb_top-cellsize);
				self.ctxText(ctx,"x\u{2081}",tb_left-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize*3/4);
				self.ctxText(ctx,"x\u{2082}x\u{2083}",tb_left-cellsize+cellsize-4*cellsize/8, tb_top-5*cellsize/8,fontsize*3/4);
			}
		}
		else if(self.argscnt==4) {
			self.ctxLine(ctx, tb_left-cellsize, tb_top,            tb_left+4*cellsize, tb_top);
			self.ctxLine(ctx, tb_left-cellsize, tb_top+2*cellsize, tb_left+4*cellsize, tb_top+2*cellsize);
			self.ctxLine(ctx, tb_left-cellsize, tb_top+4*cellsize, tb_left+4*cellsize, tb_top+4*cellsize);
			
			if(type=="V") {
				self.ctxLine(ctx, tb_left, tb_top+cellsize,            tb_left+5*cellsize, tb_top+cellsize);
				self.ctxLine(ctx, tb_left, tb_top+3*cellsize, tb_left+5*cellsize, tb_top+3*cellsize);
				
				
				self.ctxLine(ctx, tb_left, tb_top-cellsize, tb_left, tb_top+4*cellsize);
				self.ctxLine(ctx, tb_left+2*cellsize, tb_top-cellsize, tb_left+2*cellsize, tb_top+4*cellsize);
				self.ctxLine(ctx, tb_left+4*cellsize, tb_top-cellsize, tb_left+4*cellsize, tb_top+4*cellsize);
				
				self.ctxLine(ctx, tb_left+cellsize, tb_top, tb_left+cellsize, tb_top+5*cellsize);
				self.ctxLine(ctx, tb_left+3*cellsize, tb_top, tb_left+3*cellsize, tb_top+5*cellsize);
				
				self.ctxText(ctx,"x\u{0305}\u{2081}",tb_left-3*cellsize/4, tb_top+3/2*cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"x\u{2081}",tb_left-3*cellsize/4, tb_top+7/2*cellsize-cellsize/4,fontsize);
				
				self.ctxText(ctx,"x\u{0305}\u{2083}",tb_left+cellsize*3/2-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"x\u{2083}",tb_left+cellsize*7/2-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				
				self.ctxText(ctx,"x\u{0305}\u{2084}",tb_left+cellsize-3*cellsize/4, tb_top+4*cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"x\u{2084}",tb_left+cellsize*5/2-3*cellsize/4, tb_top+4*cellsize+cellsize-cellsize/4,fontsize);			
				self.ctxText(ctx,"x\u{0305}\u{2084}",tb_left+cellsize*4-3*cellsize/4, tb_top+4*cellsize+cellsize-cellsize/4,fontsize);			
				
				self.ctxText(ctx,"x\u{0305}\u{2082}",tb_left+5*cellsize-3*cellsize/4, tb_top+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"x\u{2082}",tb_left+5*cellsize-3*cellsize/4, tb_top+cellsize*3/2+cellsize-cellsize/4,fontsize);			
				self.ctxText(ctx,"x\u{0305}\u{2082}",tb_left+5*cellsize-3*cellsize/4, tb_top+cellsize*3+cellsize-cellsize/4,fontsize);				
			}
			else if(type=="K"){
				self.ctxLine(ctx, tb_left-cellsize, tb_top+cellsize,            tb_left+4*cellsize, tb_top+cellsize);
				self.ctxLine(ctx, tb_left-cellsize, tb_top+3*cellsize, tb_left+4*cellsize, tb_top+3*cellsize);
				
				self.ctxLine(ctx, tb_left, tb_top-cellsize, tb_left, tb_top+4*cellsize);				
				self.ctxLine(ctx, tb_left+cellsize, tb_top-cellsize, tb_left+cellsize, tb_top+4*cellsize);
				self.ctxLine(ctx, tb_left+2*cellsize, tb_top-cellsize, tb_left+2*cellsize, tb_top+4*cellsize);
				self.ctxLine(ctx, tb_left+3*cellsize, tb_top-cellsize, tb_left+3*cellsize, tb_top+4*cellsize);
				self.ctxLine(ctx, tb_left+4*cellsize, tb_top-cellsize, tb_left+4*cellsize, tb_top+4*cellsize);
				
				self.ctxLine(ctx,tb_left,tb_top,tb_left-cellsize,tb_top-cellsize);
				self.ctxText(ctx,"x\u{2081}x\u{2082}",tb_left-cellsize, tb_top-cellsize+cellsize-2*cellsize/8,fontsize*3/4);
				self.ctxText(ctx,"x\u{2083}x\u{2084}",tb_left-cellsize+cellsize-4*cellsize/8, tb_top-5*cellsize/8,fontsize*3/4);
				
				self.ctxText(ctx,"00",tb_left-3*cellsize/4, tb_top+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"01",tb_left-3*cellsize/4, tb_top+2*cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"11",tb_left-3*cellsize/4, tb_top+3*cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"10",tb_left-3*cellsize/4, tb_top+4*cellsize-cellsize/4,fontsize);
				
				self.ctxText(ctx,"00",tb_left+cellsize-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"01",tb_left+2*cellsize-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"11",tb_left+3*cellsize-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
				self.ctxText(ctx,"10",tb_left+4*cellsize-3*cellsize/4, tb_top-cellsize+cellsize-cellsize/4,fontsize);
			}
		}
		
		for(var i=0;i<minterms.length;i++) {
			var mid = minterms[i].id;
			var pos = this.mintermspos[this.argscnt][mid];					
			self.ctxText(ctx,"m"+sub(mid),tb_left+cellsize+pos[1]*cellsize-3*cellsize/4, tb_top+pos[0]*cellsize+cellsize-cellsize/4,fontsize);			
		}		
	}
	
	this.ctxLine =function(ctx,x0,y0,x1,y1,strokeStyle="black") {		
		ctx.strokeStyle=strokeStyle;
		ctx.beginPath();
		ctx.moveTo(x0,y0);
		ctx.lineTo(x1,y1);
		ctx.stroke();
	}
	
	this.ctxText = function(ctx,text,x,y,size,fillStyle="black") {
		ctx.font = size+'px Arial';
		ctx.fillStyle=fillStyle;
		ctx.fillText(text, x, y);
	}
	
	
}

function BoolSimplifierSolver(argscnt, values, method="V") {
	this.argscnt = argscnt;
	this.values = values;
	this.method = method;
	
	this.minterms = [];	
	
	for(var i=0;i<values.length;i++) {
		if(values[i]==1){
			this.minterms.push(new Minterm(argscnt,i));
		}
	}
	
	var self=this;
	
	this.getMintermsListString = function(){
		var str="";
		
		for(i=0;i<self.minterms.length;i++) {
			str+=self.minterms[i].name+"="+self.minterms[i].explicitForm+"<br/>";
		}
		
		return str;
	}
	
	this.performs2_4 = false;
	this.veitch_diagram_url = "";
	
	// create virtual canvas
	this.vcanvas = document.createElement('canvas');	
	this.vcanvas.width = 800;
	this.vcanvas.height = 800;
	this.vcanvas.style.zIndex = 8;
	this.vcanvas.style.position = "absolute";
	this.vcanvas.style.border = "1px solid";
	this.vcanvas.style.display="none";
	var body = document.getElementsByTagName("body")[0];
	body.appendChild(this.vcanvas);
	this.vctx = this.vcanvas.getContext("2d");
	
    this.maxterms = [];
    this.centralMonoms = [];
    
    
	this.maxtermsHTML="";    
    this.maximalMonomsSetHTML = "";
    this.centralMonomsSetHTML = "";
    this.simplificationCase = 0;
    
    this.createMaximalMonomsSetString = function() {
        var maxs = [];     
        for(var i=0;i<self.maxterms.length;i++) {
            maxs.push("max"+sub(i+1));
        }
        self.maximalMonomsSetHTML=`M(f) = {${maxs.join(", ")}}`;     
    }
    
    this.createCentralMonomsSetString = function() {
        var cens = [];     
        for(var i=0;i<self.centralMonoms.length;i++) {
            cens.push("max"+sub(self.centralMonoms[i]+1));
        }
        self.centralMonomsSetHTML=`C(f) = {${cens.join(", ")}}`;
    }
    
    this.determineCase = function() {
        if(self.centralMonoms.length == self.maxterms.length) {
            return 1;
        }
        if(self.centralMonoms.length == 0) {
            return 3;
        }
        return 2;
    }
    
    this.findCentralMonoms = function() {
        self.centralMonoms = [];
        var frq=new Array(256);
        for(var i=0;i<256;i++) frq[i]=0;
        
        for(var i=0;i<self.maxterms.length;i++) {            
            for(var j=0;j<self.maxterms[i].length;j++) {
                frq[self.maxterms[i][j]]++;
            }
        }
        
        
        for(var i=0;i<self.maxterms.length;i++) {   
            var found1=false;
            for(var j=0;j<self.maxterms[i].length && !found1;j++) {
                found1 = (frq[self.maxterms[i][j]]==1);
            }
            if(found1) self.centralMonoms.push(i);
        }             
    }    
	
	this.h_funcs = [];
	this.sols23 = [];
	
	this.compute = function(quine=false) {
		if(!quine) {
			self.clearCanvas();
			var veitch = new VeitchTable(self.argscnt,self.minterms);
			veitch.drawToContext(self.vctx,800,800,100,self.method);
			self.maxterms = veitch.getMaxterms();						
			self.findCentralMonoms();
		}else{			
			self.qBuildTable1();
			self.qBuildTable2();
			
			self.clearCanvas();
			var veitch = new VeitchTable(self.argscnt,self.minterms);
			veitch.drawToContext(self.vctx,800,800,100,self.method);			
			self.findCentralMonoms();
		}
		self.createMaximalMonomsSetString();
		self.maxtermsHTML = veitch.getMaxtermsList();
        self.createCentralMonomsSetString();
        self.simplificationCase = self.determineCase();
		
		if(self.simplificationCase != 1) {
		
			var f = new BooleanFunction(self.argscnt);
			for(var i=0;i<self.maxterms.length;i++) {				
				f.maxterms.push(new Maxterm(self.argscnt, self.maxterms[i]));
			}		
			
			var g = new BooleanFunction(self.argscnt);
			for(var i=0;i<self.centralMonoms.length;i++) {				
				g.maxterms.push(new Maxterm(self.argscnt, self.maxterms[self.centralMonoms[i]]));
			}
			
			var Sf = f.getSupport();			
			var Sg = g.getSupport();			
			
			var sH = [];
			for(var i=0;i<Sf.length;i++) {
				if(!Sg.includes(Sf[i])) {
					sH.push(Sf[i]);
				}
			}			
			
			hs = findMaxtermsCase23(sH,self.maxterms);	
			for(var i=0;i<hs.length;i++) {
				var parH = [];				
									
				for(var j=0;j<hs[i].length;j++) {
					parH.push(hs[i][j]);			
				}
				
				self.h_funcs.push(parH);				
			}
			//console.log(self.h_funcs);		

			for(var i=0;i<self.h_funcs.length;i++) {
				var h = self.h_funcs[i];
				var sol = [];
				for(var j=0;j<self.centralMonoms.length;j++) {
					sol.push(new Maxterm(self.argscnt, self.maxterms[self.centralMonoms[j]], self.centralMonoms[j]+1));
				}
				for(var j=0;j<h.length;j++) {
					sol.push(new Maxterm(self.argscnt, self.maxterms[h[j]], h[j]+1));
				}
				sol.sort((x,y)=>x.id-y.id);
				self.sols23.push(sol);						
							
			}									
		}		
	}
		
	this.sols23HTML = function() {
		var result = [];		
		for(var i=0;i<self.sols23.length;i++) {
			var res = "f"+sub(i+1)+" = ";
			var maxs = [];
			var expls = [];			
			for(var j=0;j<self.sols23[i].length;j++) {
				maxs.push(self.sols23[i][j].name);
				
				
				expls.push(self.sols23[i][j].explicitForm());
			}
			res+=maxs.join("&#x2228;") + " = " + expls.join("&#x2228;");
			result.push(res);			
		}		
		return result.join("<br/>");
	}
	
	this.hFuncsHTML = function() {
		var result = [];
				
		for(var i=0;i<self.h_funcs.length;i++) {
			var sol = "h"+sub(i+1)+" = ";
			var terms = [];
			for(var j=0;j<self.h_funcs[i].length;j++)
				terms.push("max"+sub(self.h_funcs[i][j]+1));
			sol += terms.join("&#x2228;");
			result.push(sol);
		}
		
		return result.join("<br/>");
	}
	
	this.clearCanvas = function() {		
		self.vctx.clearRect(0, 0, self.vcanvas.width, self.vcanvas.height);		
	}	
	
	this.canvas64 = function() {
		return self.vcanvas.toDataURL();
	}
	
	this.getFuncWithParamsHTML = function(fname) {
		var xlist = [];
		for(var i=0;i<self.argscnt;i++) {
			xlist.push("x"+sub(i+1));
		}
		return fname+"("+xlist.join(",")+")";
	}
	
	this.maxDisjointHTML = function(maxterm) {
		var mlist = [];
		for(var i=0;i<self.maxterms.length;i++) {
			mlist.push("max"+sub(i+1));
		}	
		return mlist.join(" \u2228 ");
	}
	
	this.maxDisjointExplicitHTML = function() {
		var mlist = [];
		for(var i=0;i<self.maxterms.length;i++) {			
			mlist.push("max"+sub(i+1));
		}	
		return mlist.join(" \u2228 ");
	}

	this.minsDisjointHTML = function() {
		var mlist = [];
		for(var i=0;i<self.minterms.length;i++) {
			mlist.push("m"+sub(self.minterms[i].id));
		}	
		return mlist.join(" \u2228 ");
	}
	
	this.minsDisjointExplicitHTML = function() {
		var mlist = [];
		for(var i=0;i<self.minterms.length;i++) {
			mlist.push(self.minterms[i].explicitForm);
		}	
		return mlist.join(" \u2228 ");
	}
	
	this.censDisjointHTML = function() {
		var mlist = [];
		for(var i=0;i<self.centralMonoms.length;i++) {
			mlist.push("max"+sub(self.centralMonoms[i]+1));
		}	
		return mlist.join(" \u2228 ");
	}
	
	this.qTable1 = null;
	this.qTable2 = null;
	
	this.qOrderedSupport = [];
	
	this.qBuildTable1 = function() {
		console.log(self.values);
		for(var i=0;i<self.values.length;i++) {
			if(self.values[i]) self.qOrderedSupport.push(i);
		}
		self.qOrderedSupport.sort((x,y)=> {
			var bitsx=getBits(x,self.argscnt);
			var bitsy=getBits(y,self.argscnt);
			var n1x=0, n1y=0;
			for(var i=0;i<self.argscnt;i++) {
				n1x+=bitsx[i]==1;
				n1y+=bitsy[i]==1;
			}
			if(n1x!=n1y) return n1x-n1y;
			return x-y;
		});
		console.log(self.qOrderedSupport);
				
		var tgroups = new Array(self.argscnt+1);
		for(var i=0;i<=self.argscnt;i++) tgroups[i]=[];
					
		for(var i=0;i<self.qOrderedSupport.length;i++) {
			var bits=getBits(self.qOrderedSupport[i],self.argscnt);
			var n1=0;
			for(var j=0;j<self.argscnt;j++) {
				n1+=(bits[j]==1);
			}
			tgroups[n1].push(self.qOrderedSupport[i]);
		}
		
		//console.log(tgroups);
		
		var tdata = [];				
		var grouptag=1;
		for(var i=0;i<=self.argscnt;i++) {			
			if(tgroups[i].length>0) {
				for(var j=0;j<tgroups[i].length;j++) {
					var trow = {};
					trow.grouptag = grouptag;
					trow.data = getBits(tgroups[i][j],self.argscnt);					
					trow.minterms = [tgroups[i][j]];
					trow.description = "m"+sub(tgroups[i][j]);
					trow.checked=false;
					tdata.push(trow);					
				}				
				grouptag++;
			}			
		}		
		//console.log(tdata);
				
		var crtgroup = 1;
		var crtsolved = 0;		
		for(var i=0;i<tdata.length;i++) {		
			if(tdata[i].grouptag!=crtgroup) {
				crtgroup=tdata[i].grouptag;
				if(crtsolved>0) {
					grouptag++;
				}
				crtsolved=0;
			}			
			for(var j=i+1;j<tdata.length;j++) {				
				if(tdata[i].grouptag+1==tdata[j].grouptag) {							
					var res = solve(tdata[i], tdata[j]);										
										
					if(res!=false) {
						res.grouptag=grouptag;
						
						var duplicate=false;
						for(var k=0;k<tdata.length && !duplicate;k++) {
							var rw = tdata[k];
							if(rw.grouptag==res.grouptag) {			
								var ok=true;
								for(var p=0;p<self.argscnt && ok;p++) {
									if(rw.data[p]!=res.data[p]) ok=false;
								}
								if(ok) duplicate=true;
							}
						}
						tdata[i].checked=tdata[j].checked=true;
						if(!duplicate){													
							console.log(res);
							tdata.push(res);
							crtsolved++;
						}
					}
				}
			}					
		}
		
		self.maxterms=[];
		for(var i=0;i<tdata.length;i++) {
			if(tdata[i].checked) {
				tdata[i].checked="&#x2713;"
			}
			else {
				tdata[i].minterms.sort((a,b)=>{return a-b;});
				var mins=[];
				for(var j=0;j<tdata[i].minterms.length;j++) mins.push(tdata[i].minterms[j]);
				self.maxterms.push(mins);
				tdata[i].checked="max"+sub(self.maxterms.length)+"=";
				for(var j=0;j<self.argscnt;j++) {
					if(tdata[i].data[j]!="-"){
						tdata[i].checked+="x";
						if(tdata[i].data[j]==0){
							tdata[i].checked+="&#773;"
						}
						tdata[i].checked+=sub(j+1);
					}
				}
			}
		}
		
		function solve(p,q) {
			var diff=0, pos;
			for(var i=0;i<self.argscnt;i++) {
				if(p.data[i]=="-") {
					if(q.data[i]!="-") return false;					
				}
				if(q.data[i]=="-") {
					if(p.data[i]!="-") return false;
				}
				if(p.data[i]!=q.data[i]) {
					diff++;
					pos=i;
				}								
			}
			if(diff!=1) return false;
			var row={};
			row.data=[];
			for(var i=0;i<self.argscnt;i++) {
				row.data.push(p.data[i]);
			}
			row.data[pos]="-";
			var left=p.description;
			var right=q.description;
			if(p.minterms.length>1) left="("+left+")";
			if(q.minterms.length>1) right="("+right+")";
			row.description = left+"&#x2228"+right;
			row.minterms=[];
			for(var i=0;i<p.minterms.length;i++) row.minterms.push(p.minterms[i]);
			for(var i=0;i<q.minterms.length;i++){
				if(!row.minterms.includes(q.minterms[i])){
					row.minterms.push(q.minterms[i]);
				}
			}
			row.checked=false;
			return row;
		}
		
		var table = document.createElement("table");
		table.className="table-bordered table-black";
		var header = document.createElement("tr");	
		header.appendChild(document.createElement("th"));		
		for(var i=0;i<self.argscnt;i++) {
			var th = document.createElement("th");
			th.innerHTML = "x"+sub(i+1);
			header.appendChild(th);
		}				
		header.appendChild(document.createElement("th"));
		header.appendChild(document.createElement("th"));
		table.appendChild(header);
		
		var	lastgroup=-1;
		for(var i=0;i<tdata.length;i++) {
			var tr=document.createElement("tr");					
			if(lastgroup!=tdata[i].grouptag) {				
				if(lastgroup!=-1) addEmptyRow();
				lastgroup = tdata[i].grouptag;				
				var td=document.createElement("td");
				td.innerHTML="<i>"+GroupTagsStr[tdata[i].grouptag]+"</i>";
				td.style.padding="5px";
				var q=0;
				for(;i+q<tdata.length && tdata[i+q].grouptag==lastgroup;q++);
				td.setAttribute("rowspan",q);
				tr.appendChild(td);
			} else {				
			}
			for(var j=0;j<tdata[i].data.length;j++) {				
				var td=document.createElement("td");
				td.innerHTML=tdata[i].data[j];
				tr.appendChild(td);							
			}
			
			var td=document.createElement("td");
			td.innerHTML=tdata[i].description;//minterms.map(id=>"m"+sub(id)).join("&#x2888;");
			tr.appendChild(td);					

			var td=document.createElement("td");
			td.innerHTML=tdata[i].checked;
			tr.appendChild(td);								
			
			table.appendChild(tr);
		}
		addEmptyRow();
		addEmptyRow();
		
		self.qTable1 = document.createElement("center");
		self.qTable1.appendChild(table);
		
		
		function addEmptyRow() {
			var row=document.createElement("tr");			
			row.style.height="3px";
			var cell = document.createElement("td");
			cell.setAttribute("colspan",self.argscnt+2);
			row.appendChild(cell);
			table.appendChild(row);
		}
	}	
	
	this.qBuildTable2 = function() {
		
		var usedmins = [];
		
		for(var i=0;i<self.maxterms.length;i++) {
			for(var j=0;j<self.maxterms[i].length;j++) {
				if(!usedmins.includes(self.maxterms[i][j])) {
					usedmins.push(self.maxterms[i][j]);
				}
			}
		}
		usedmins.sort((a,b)=>{return a-b;});
		
		var tdata=new Array(usedmins.length);
		for(var i=0;i<tdata.length;i++) {
			tdata[i]=[];
			var starscount=0;
			var starpos=0;
			for(var j=0;j<self.maxterms.length;j++) {
				if(self.maxterms[j].includes(usedmins[i])) {
					tdata[i].push(["&#9733;",false,false]); // text, circled, background
					starscount++;
					starpos=j;					
				}
				else {
					tdata[i].push(["",false,false]);
				}				
			}
			if(starscount==1){
				tdata[i][starpos][0]="&#9055;";
				tdata[i][starpos][1]=true;
			}
		}			
		
		for(var i=0;i<tdata.length;i++) {
			for(var j=0;j<self.maxterms.length;j++) {
				if(tdata[i][j][1]) {
					for(var k=0;k<tdata.length;k++) {
						tdata[k][j][2]=true;
					}
				}
			}
		}		
		
		for(var i=0;i<tdata.length;i++) {
			for(var j=0;j<self.maxterms.length;j++) {
				if(tdata[i][j][0]!="" && tdata[i][j][2]) {
					for(var k=0;k<self.maxterms.length;k++) {
						tdata[i][k][2]=true;
					}
				}
			}
		}		
		
		console.log(tdata);
		
		var table = document.createElement("table");
		table.className="table-bordered table-black";
		var header = document.createElement("tr");
		var corner= document.createElement("th");
		corner.innerHTML="m\\M";
		header.appendChild(corner);
		for(var i=0;i<self.maxterms.length;i++) {
			var cell=document.createElement("th");
			cell.innerHTML="max"+sub(i+1);
			var bkgcnt=0;
			for(var j=0;j<tdata.length;j++) {
				bkgcnt+=tdata[j][i][2];
			}
			if(bkgcnt==tdata.length) {
				cell.style.background = "#FFC30B";
			}
			header.appendChild(cell);
		}
		table.appendChild(header);
		
		for(var i=0;i<usedmins.length;i++) {
			var tr=document.createElement("tr");
			
			var th=document.createElement("th")
			th.innerHTML="m"+sub(usedmins[i]);		
	
			var bkgcnt=0;
			for(var j=0;j<self.maxterms.length;j++) {
				bkgcnt+=tdata[i][j][2];
			}
			if(bkgcnt==self.maxterms.length) {
				th.style.background = "#FFC30B";
			}
			
			tr.appendChild(th);
			
			for(var j=0;j<self.maxterms.length;j++) {
				var td=document.createElement("td");
				td.style.textAlign="center";
				td.style.fontWeight="bold";
				td.innerHTML=tdata[i][j][0];
				if(!tdata[i][j][1]){
					td.style.fontSize="11px";
				}
				if(tdata[i][j][2]) {
					td.style.background="#FFC30B";
				}
				tr.appendChild(td);
			}
			
			table.appendChild(tr);
		}		
		
		self.qTable2 = document.createElement("center");
		self.qTable2.appendChild(table);
	}
}

const GroupTagsStr = ["?", "I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX", "X", "XI", "XII", "XIII", "XIV", "XV", "XVI", "XVII", "XVIII", "XIX", "XX", "XXI", "XXII"];


function getBits(n,lstcnt) {
	lst = [];
	while(n>0 && lst.length<lstcnt) {				
		lst.push(n%2);
		n=Math.floor(n/2);
	}
	while(lst.length<lstcnt) {				
		lst.push(0);			
	}
	
	lst.reverse();
	return lst;
}
		
