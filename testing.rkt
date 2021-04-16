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
option max_tracelength 10

sig Person {
	// a predetermined queue of potential people
	next: lone Person
}

one sig NextPersonTracker{
	// keeps track of the next person (not in our system yet)
	var nextPerson: lone Person
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
	var numVaccines: one Int,
	var productionStage: one Int
	// consider keeping track of different vaccines, for example first dose vs. second dose
}

one sig obsRoom extends Room {
}

// keeps track of time, starts at 0
one sig Clock{
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
	Clock.timer = sing[0]

	/*
	#(Ballpark.people) = 5
	some head: Person | {
		no next.head
		// points to the next person in line (haven't arrived at Ballpark yet)
		NextPersonTracker.nextPerson = head.next.next.next.next.next
		Ballpark.people = head + head.next + head.next.next + head.next.next.next + head.next.next.next.next
	}
	*/

	// 2 persons
	/* #(Ballpark.people) = 2
	some head: Person | {
		no next.head
		// points to the next person in line (haven't arrived at Ballpark yet)
		NextPersonTracker.nextPerson = head.next.next
		Ballpark.people = head + head.next
	} */

	// 1 person
	#(Ballpark.people) = 1
	some head: Person | {
		no next.head
		// points to the next person in line (haven't arrived at Ballpark yet)
		NextPersonTracker.nextPerson = head.next
		Ballpark.people = head
	}
	// all other rooms are empty
	no (people - Ballpark->Person)
	// room capacities
	initCapacity
	// num vaccines = 6
	vacRoom.numVaccines = sing[6]
	vacRoom.productionStage = sing[0]
	// people is in some linear order
	//isQueue
}

// maybe not enforce
pred roomConstraints{
	// must have some people in a line
	// cannot be over capacity
}

// ====== Transitions ========

// 5 minutes goes by
pred doNothing {
	// everything stays the same

	people' = people
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	Clock.timer' = sing[add[sum[Clock.timer], 1]]

	// making the vaccine every 3 cycles
	vacRoom.productionStage = sing[3] implies vacRoom.productionStage' = sing[2]
	vacRoom.productionStage = sing[2] implies vacRoom.productionStage' = sing[1]
	vacRoom.productionStage = sing[1] implies vacRoom.productionStage' = sing[0]
	vacRoom.productionStage = sing[0] implies vacRoom.productionStage' = sing[0]

	vacRoom.productionStage = sing[1] implies vacRoom.numVaccines' = sing[add[sum[vacRoom.numVaccines], 6]]
	vacRoom.productionStage != sing[1] implies vacRoom.numVaccines' = vacRoom.numVaccines

}



// need to make sure that only one transistion happens (one person moves) in each state
pred addToBallpark{
	// add ppl to the ballpark
	// or
	// P goes from ballpark to waiting room, then
	// Ballpark.people - P = Ballpark.people’  or  Ballpark.people - P + lastPerson.next= Ballpark.people’
	// else Ballpark.people = Ballpark.people’ or Ballpark.people + lastPerson.next = Ballpark.people’
	some NextPersonTracker.nextPerson
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson.next
	people' = people + Ballpark->NextPersonTracker.nextPerson
	vacRoom.numVaccines' = vacRoom.numVaccines
	Clock.timer' = Clock.timer
	vacRoom.productionStage = vacRoom.productionStage'
}

pred ballToWaitingGuard{
	// waiting room must have room
	#(waitingRoom.people) < sum[waitingRoom.capacity]
	some p: Person | { p in Ballpark.people }
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
	Clock.timer' = Clock.timer
	vacRoom.productionStage = vacRoom.productionStage'
}

pred waitingToVacGuard{
	// vaccination room must have room
	#(vacRoom.people) < sum[vacRoom.capacity]
	#numVaccines > 0
	some p: Person | { p in waitingRoom.people }
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
	vacRoom.numVaccines' = sing[subtract[sum[vacRoom.numVaccines], 1]]
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	Clock.timer' = Clock.timer
	vacRoom.productionStage = vacRoom.productionStage'
}

pred vacToObsGuard{
	before doNothing
	#(obsRoom.people) < sum[obsRoom.capacity]
}

pred vacToObs{
	// now we assume that vaccine takes one cycle (same time as doNothing) to be shot, and people can only come in at the beginning of the cycle

	vacToObsGuard
	vacRoom.numVaccines' = vacRoom.numVaccines
	people' = people - vacRoom->Person + obsRoom->(vacRoom.people)
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	Clock.timer' = Clock.timer
	vacRoom.productionStage = vacRoom.productionStage'
}

pred obsToExitGuard{
	some p: Person | {
		once (doNothing and once (doNothing and once (doNothing and once (doNothing and p in obsRoom.people))))
	}
}

pred obsToExit{
	obsToExitGuard

	// once (doNothing and once(doNothing and once (doNothing and once p in obsRoom))) then move p to exit
	some p: Person | {
		once (doNothing and once (doNothing and once (doNothing and once (doNothing and p in obsRoom.people))))
		people' = people - obsRoom->p
	}

	vacRoom.numVaccines' = vacRoom.numVaccines
	Clock.timer' = Clock.timer
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	vacRoom.productionStage = vacRoom.productionStage'
}

pred makeVacGuard {
	#waitingRoom.people > sum[vacRoom.numVaccines]
	vacRoom.productionStage = sing[0] // no vaccine is getting made
}

pred makeVaccines {
	// max 6 every 3 states
	// similar to requests on elevator

	makeVacGuard

	vacRoom.productionStage' = sing[3]
	vacRoom.numVaccines' = vacRoom.numVaccines
	// vacRoom.numVaccines' = sing[sum[vacRoom.numVaccines, sing[6]]]
	people' = people
	Clock.timer' = Clock.timer
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
}

pred doAbosolutelyNothing{
	people' = people
	Clock.timer' = Clock.timer
	vacRoom.numVaccines' = vacRoom.numVaccines
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	vacRoom.productionStage' = vacRoom.productionStage
}

pred traces{
	// run everything
	/*
	init
	addToBallpark
	after ballToWaiting
	after after ballToWaiting
	after after after waitingToVac
	after after after after waitingToVac
	after after after after after doNothing
	after after after after after after vacToObs
	after after after after after after after doNothing
	after after after after after after after after doNothing
	after after after after after after after after after doNothing
	after after after after after after after after after after doNothing
	after after after after after after after after after after after obsToExit
	after after after after after after after after after after after after obsToExit
	after after after after after after after after after after after after after doNothing
	*/

	init
	/* always (addToBallpark or ballToWaiting or waitingToVac or vacToObs or obsToExit or (doNothing and not ballToWaitingGuard and not waitingToVacGuard and not vacToObsGuard and not obsToExitGuard and not makeVacGuard)) */

	// // always (addToBallpark or ballToWaiting or waitingToVac or vacToObs or obsToExit or doNothing)
	// ballToWaiting
	// after waitingToVac
	// after after doNothing
	// after after after vacToObs
	// after after after after doNothing
	// after after after after after doNothing
	// after after after after after after doNothing
	// after after after after after after after doNothing
	// after after after after after after after after obsToExit
	// after after after after after after after after after always (doAbosolutelyNothing and no people and no NextPersonTracker.nextPerson)


	always (ballToWaiting or waitingToVac or vacToObs or obsToExit or doNothing or (doAbosolutelyNothing and no people and no NextPersonTracker.nextPerson))
}

run {traces} for exactly 1 Person, 5 Int
