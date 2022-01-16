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
		
