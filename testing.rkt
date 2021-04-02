#lang forge
// capacities: WR 4, VR 2, OR 5
// People A → B → C

// Create 10 Person
// 5 start in ballpark
// # (people) < capacity

// doNothing is 5 minutes
// vacRoom 5 minutes
// obsRoom stay 20 minutes

option problem_type temporal
option max_tracelength 40

sig Person {
	// a predetermined queue of potential people
	next: lone Person
}

one sig NextPersonTracker{
	// keeps track of the next person (not in our system yet)
	var nextPerson: one Person
}

abstract sig Room {
	var people: set Person,
	capacity: one Int
} 

// has queues
one sig Ballpark extends Room {}
// has queues
one sig waitingRoom extends Room{}

// doesn’t need queues
one sig vacRoom extends Room {
	var numVaccines: one Int
	// consider keeping track of different vaccines, for example first dose vs. second dose
}

one sig obsRoom extends Room {
}

// keeps track of time, starts at 0
one sig Time{
	var timer: one Int
}

// methods:
// ***STATE CHANGE is 5 minutes ****
// (for waiting: make a doNothing for each room (each state has a different time amt))  

pred isQueue {
	some head: Person | some tail: Person{
		all p: (Person - head) | one next.p
		all p: (Person - tail) | one p.next
		no next.head
		one head.next
		no tail.next
		one next.tail
		head.*next = Person
	}
}

pred initCapacity{
	Ballpark.capacity = sing[10]
	waitingRoom.capacity = sing[4]
	vacRoom.capacity = sing[2]
	obsRoom.capacity = sing[5]
}

pred init {
	// Ballpark queue = 5 ppl
	Time.timer = sing[0]
	#(Ballpark.people) = 5
	some head: Person | {
		no next.head
		// points to the next person in line (haven't arrived at Ballpark yet)
		NextPersonTracker.nextPerson = head.next.next.next.next.next
		Ballpark.people = head + head.next + head.next.next + head.next.next.next + head.next.next.next.next
	}
	// all other rooms are empty
	no (people - Ballpark->Person)
	// room capacities
	initCapacity
	// num vaccines = 6
	vacRoom.numVaccines = sing[6]
	// people is in some linear order
	isQueue
}

// maybe not enforce
pred roomConstraints{
	// must have some people in a line
	// cannot be over capacity
}

// ====== Transitions ========

// need to make sure that only one transistion happens (one person moves) in each state

pred addToBallpark{
	// add ppl to the ballpark
	// or
	// P goes from ballpark to waiting room, then
	// Ballpark.people - P = Ballpark.people’  or  Ballpark.people - P + lastPerson.next= Ballpark.people’
	// else Ballpark.people = Ballpark.people’ or Ballpark.people + lastPerson.next = Ballpark.people’
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson.next
	people' = people + Ballpark->NextPersonTracker.nextPerson
	vacRoom.numVaccines' = vacRoom.numVaccines
	Time.timer' = Time.timer
}

pred ballToWaitingGuard{
	// waiting room must have room
	#(waitingRoom.people) < sum[waitingRoom.capacity]
}

pred ballToWaiting{
	// now at the head of the ballpark queue
	ballToWaitingGuard
	some p: Person | {
		p in Ballpark.people
		(no next.p) or (next.p not in Ballpark.people)
		people' = people - Ballpark->p + waitingRoom->p
	}
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	vacRoom.numVaccines' = vacRoom.numVaccines
	Time.timer' = Time.timer
}

pred waitingToVacGuard{
	// vaccination room must have room
	#(vacRoom.people) < sum[vacRoom.capacity]
	#numVaccines > sing[0]
}

pred waitingToVac {
	// you must be at the head of the waiting room queue 

	// TODO: if Vac is (full - 1),  else just go thru
	waitingToVacGuard
	some p: Person | {
		p in waitingRoom.people
		(no next.p) or (next.p not in waitingRoom.people)
		people' = people - waitingRoom->p + vacRoom->p
	}
	// subtract 1 from #vaccines
	#numVaccines' = subtract[sum[#numVaccines], 1]
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	Time.timer' = Time.timer
}

pred vacToObsGuard{
	before doNothing
	#(obsRoom.people) < sum[obsRoom.capacity]
}

pred vacToObs{
	// before doNothing and in vacRoom
	// before doNothing
	// before before you must be waitingToVac
	vacToObsGuard
	vacRoom.numVaccines' = vacRoom.numVaccines
	people’ = people - vacRoom->Person + obsRoom->(vacRoom.people)
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	Time.timer' = Time.timer
}

pred obsToExitGuard{

}

pred obsToExit{
	obsToExitGuard

	// once (doNothing and once(doNothing and once (doNothing and once p in obsRoom))) then move p to exit
	// before, you must do vacToObs
	// person must be here for 2 states
	vacRoom.numVaccines' = vacRoom.numVaccines
	Time.timer' = Time.timer
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson

}

pred makeVaccines {
	// max 6 every 3 states
	// similar to requests on elevator
	
	Time.timer' = Time.timer
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
}

// 5 minutes goes by
pred doNothing {
	// everything stays the same
	not ballToWaitingGuard
	not waitingToVacGuard
	not vacToObsGuard
	not obsToExitGuard
	people' = people
	vacRoom.numVaccines' = vacRoom.numVaccines
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	Time.timer' = sing[sum[Time.timer, sing[1]]]
}

pred traces{
	// run everything
	init
	addToBallpark
	after ballToWaiting
	after after ballToWaiting
	// always (addToBallpark or ballToWaiting or doNothing)
}

run {traces} for exactly 10 Person, 8 Int
