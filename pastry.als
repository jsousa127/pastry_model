open util/integer
open util/ordering[Id]
sig Time {}

one sig Max in Int {}
sig Id {
	succ : one Id	
}
sig Data {}

sig Key {
    node : lone Node
}

abstract sig State {}
one sig Ready, Wait, Ok extends State {} 

sig Node {
    id : one Id,
    state : one State,
    data : one Data,
    left : Node,
    right : Node,
    lData :  Node -> Data,
    rData :  Node -> Data,
    routing : Key -> one Id
} {
    #left = #right && #left = Max
	 
        Data.~lData = left
        Data.~rData = right
	this not in left + right

}

fact {
	left.id = id.succ
	right.id = id.~succ
    id . ~id in iden
    data . ~data in iden
    no (left & right)
Node.(lData + rData) in data
   
}

fact ring { 
	all i : Id | Id in i.^succ
	Id in Node.id
	
}

