/* 
Each node as a set of outgoing edges, representing a directed graph without multiple edged.
*/
sig Node {
	adj : set Node
}

/*
The graph is undirected, ie, edges are symmetric.
http://mathworld.wolfram.com/UndirectedGraph.html
*/
pred undirected {
  	// adj = ~adj
	all n1, n2: Node | n1 in n2.adj implies n2 in n1.adj 
}

/*
The graph is oriented, ie, contains no symmetric edges.
http://mathworld.wolfram.com/OrientedGraph.html
*/
pred oriented {
  	// no adj & ~adj
	all n1, n2: Node | n1 in n2.adj implies n2 not in n1.adj 
}
/*
The graph is acyclic, ie, contains no directed cycles.
http://mathworld.wolfram.com/AcyclicDigraph.html
*/
pred acyclic {
  	// no iden & ^adj
	all n: Node | n not in n.^adj //(fecho transitivo)
}

/*
The graph is complete, ie, every node is connected to every other node.
http://mathworld.wolfram.com/CompleteDigraph.html
*/
pred complete {
  	adj = Node->Node //(produto cartesiano, para cadda No relaciono com outro No)
  	// all n: Node | n.adj = Node
	// all n1,n2: Node | n2 in n1.adj and n1 in n2.adj 
}

/*
The graph contains no loops, ie, nodes have no transitions to themselves.
http://mathworld.wolfram.com/GraphLoop.html
*/
pred noLoops {
	// all n:Node | n not in n.adj
  	no iden & adj 
}

/*
The graph is weakly connected, ie, it is possible to reach every node from every node ignoring edge direction.
http://mathworld.wolfram.com/WeaklyConnectedDigraph.html
*/
pred weaklyConnected {
  	// all disj n1, n2: Node | n2 in n1.^(adj + ~adj)  
	// Node->Node in *(adj + ~adj)
	all disj n1, n2: Node | n1 in n2.^(adj + ~adj)
}

/*
The graph is strongly connected, ie, it is possible to reach every node from every node considering edge direction.
http://mathworld.wolfram.com/StronglyConnectedDigraph.html
*/
pred stonglyConnected {
  	// all disj n1, n2: Node | n2 in n1.^adj
	// all n1, n2: Node | n2 in n1.*adj
	// Node->Node - iden in ^adj  
	all disj n1, n2: Node | n1 in n2.^adj //(n2.^adj = nos que é possivel chegar atraves do nó n2)
}

/*
The graph is transitive, ie, if two nodes are connected through a third node, they also are connected directly.
http://mathworld.wolfram.com/TransitiveDigraph.html
*/
pred transitive {
	// adj = ^adj
	// all a, b, c: Node | a->b in adj and b->c in adj implies a->c in adj
	// all a, b, c: Node | b in a.adj and c in b.adj implies c in a.adj
  	adj.adj in adj
}
