open util/integer
open util/ordering[Id]
open util/ordering[Time]
sig Time {}

one sig L in Int {}
one sig M in Int {}
sig Id {
	value : one Int,
	succ :  Id one -> Time	
}


sig Data {}

abstract sig Message {}
sig JoinMessage extends Message {}

sig Key {
    value : one Int,
    node : Node -> Time
} {
    lte[value, M]
    all t : Time | lone node.t
}

abstract sig State {}
one sig Ready, Wait, Ok extends State {} 

sig Node {
    id : one Id,
    state : State one -> Time,
    data : Data one -> Time,
    left : Node -> Time,
    right : Node -> Time,
    lData :  Node -> Data -> Time,
    rData :  Node -> Data -> Time,
    routing : set Node,
    mailbox : Message -> Time
} {
     lte[id.value, M]
    all t : Time {
	#left.t = #right.t && #left.t = L
    	this not in left.t + right.t
	data.~data in iden // Data is unique for every Node
    }
}

fact {
  id . ~id in iden  			// ID is unique		
    no (left & right)		
    Node.(lData + rData) in data
all t : Time {
    lData.t.Data = left.t
    rData.t.Data = right.t

}
}

fact succLeftRight {
	all t : Time {
		all n : Node, n1 : n.left.t {
			(some n2 : n.left.t | n1.id = n2.id.succ.t)
			or (n1.id = n.id.succ.t)
		}
		all n : Node, n1 : n.right.t {
			(some n2 : n.right.t | n1.id.succ.t = n2.id)
			or (n1.id.succ.t = n.id)
		}
	}
}

fact ring { 
	all t : Time {
		all i : Id | Id in i.^(succ.t)
		Id in Node.id	
	}
}

fun distance[x : Int, y : Int] : Int {
	lt[minus[x, y], negate[M]] 
		implies add[minus[x, y], M]
		else (gt[minus[x, y], M] implies minus[minus[x, y], M]
			else minus[x, y])
}

/*
fun leftNeighbour[n : Node] {
	
}

fun covers[n : Node, k : Key] {
	
}*/

pred sendMessage[m : Message, n : Node, t : Time] {
	n.mailbox.(t.next) = n.mailbox.t + m
}

pred recvMessage[m : Message, n : Node, t : Time] {
	m in n.mailbox.t
	n.mailbox.(t.next) = n.mailbox.t - m	
}

one abstract sig Event {
	pre, pos : one Time
}

/*sig Join extends Event {
	i, j : Node
} {
	j.state.pre = Wait

	some msg : JoinMessage | sendMessage[msg, i, pre]
}*/

run {
	L = 2
	M = 7
} for 8

