module exercises/prison

sig Gang {members: set Inmate}

sig Inmate {room: Cell}

sig Cell {}

//a
pred safe () {
  all x, y : Inmate | 
    members.x != members.y => x.room !=  y.room}

//b
pred happy () {
  all x, y : Gang.members | (x.room =  y.room => one members.(x+y))
}

pred show (disj x,y,z: Inmate, disj g1, g2 : Gang) {
  x in g1.members 
  y+z in g2.members
  happy
  safe
}
run show for 5 but exactly 2 Gang

//c. no one can be memer of two different gangs
fact{all disj g1, g2:Gang| no g1.members & g2.members}

//b
assert safeisappy{safe => happy}

check safeisappy for 6
