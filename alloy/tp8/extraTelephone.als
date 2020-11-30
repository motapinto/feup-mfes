module exercises/phones

sig Phone {
  requests: set Phone,
  connects: lone /*Phone,*/ requests, // every connection has a matching request
  forward: lone Phone
}{this not in requests
  this not in forward}

// no conference calls
fact{all p1,p2 : Phone | p2 in p1.connects => no p2.connects}

fact{all p : Phone | lone connects.p}

// forward
fact{all p1, p2 : Phone | p2 in p1.requests => p2.forward in p1.requests}

fact{all p : Phone | some p.forward => no connects.p}


pred show(p1,p2,p3:Phone ){
  p2 in p1.requests
  p3 in p2.forward
}

run show for 4
