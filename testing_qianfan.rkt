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
//option max_tracelength 200
option max_tracelength 100

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


// AK
pred isQueue {
    #(Person) >= 2 implies {
        no (^next) & iden
        some head: Person | some tail: Person {
            all p: (Person - head) | one next.p
            all p: (Person - tail) | one p.next
            no next.head
            one head.next
            no tail.next
            one next.tail
            head.*next = Person
        }
    }
}


// SM
pred initCapacity{
	Ballpark.capacity = sing[10]
	waitingRoom.capacity = sing[4]
	vacRoom.capacity = sing[2]
	obsRoom.capacity = sing[5]
}

// SM
pred init {
	// Ballpark queue = 5 ppl
	Clock.timer = sing[0]
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
	vacRoom.productionStage = sing[0]
	// people is in some linear order
	isQueue
}

// maybe not enforce
pred roomConstraints{
	// must have some people in a line
	// cannot be over capacity
}

// ====== Transitions ========

// QC
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

// test expect {
// 	doNothingTest0: {doNothing} is sat

// 	doNothingTest1: {
// 			some Person0, Person1, Person2 : Person | {
// 				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
// 				next = Person0 -> Person1 + Person1 -> Person2


// 				//pre
// 				Ballpark.people = Person0 + Person1
// 				no waitingRoom.people
// 				no vacRoom.people
// 				no obsRoom.people

// 				NextPersonTracker.nextPerson = Person2
// 				Clock.timer = sing[0]
// 				vacRoom.numVaccines = sing[6]
// 				vacRoom.productionStage = sing[0]


// 				//post
// 				Ballpark.people = Person0 + Person1
// 				no waitingRoom.people
// 				no vacRoom.people'
// 				no obsRoom.people'

// 				NextPersonTracker.nextPerson' = Person2
// 				Clock.timer' = sing[1]
// 				vacRoom.numVaccines' = vacRoom.numVaccines
// 				vacRoom.numVaccines = sing[6]
// 				vacRoom.productionStage = sing[0]

// 				doNothing
// 			}
// 	} is sat 

// 	doNothingTest2: {
// 			some Person0, Person1, Person2 : Person | {
// 				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
// 				next = Person0 -> Person1 + Person1 -> Person2


// 				//pre
// 				Ballpark.people = Person0 + Person1
// 				no waitingRoom.people
// 				no vacRoom.people
// 				no obsRoom.people

// 				NextPersonTracker.nextPerson = Person2
// 				Clock.timer = sing[0]
// 				vacRoom.numVaccines = sing[6]
// 				vacRoom.productionStage = sing[0]


// 				//post
// 				Ballpark.people = Person0 + Person1
// 				no waitingRoom.people
// 				no vacRoom.people'
// 				no obsRoom.people'

// 				NextPersonTracker.nextPerson' = Person2
// 				Clock.timer' = sing[0]
// 				vacRoom.numVaccines' = sing[6]
// 				vacRoom.productionStage = sing[0]

// 				doNothing
// 			}
// 	} is unsat 

// 	doNothingTest3: {
// 			some Person0, Person1, Person2 : Person | {
// 				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
// 				next = Person0 -> Person1 + Person1 -> Person2


// 				//pre
// 				Ballpark.people = Person0 + Person1
// 				no waitingRoom.people
// 				no vacRoom.people
// 				no obsRoom.people

// 				NextPersonTracker.nextPerson = Person2
// 				Clock.timer = sing[0]
// 				vacRoom.numVaccines = sing[6]
// 				vacRoom.productionStage = sing[0]

// 				//post
// 				Ballpark.people = Person0 + Person1
// 				no waitingRoom.people
// 				no vacRoom.people'
// 				no obsRoom.people'

// 				NextPersonTracker.nextPerson' = Person2
// 				Clock.timer' = sing[1]
// 				vacRoom.numVaccines' = sing[5]
// 				vacRoom.productionStage = sing[0]

// 				doNothing
// 			}
// 	} is unsat 

// 	doNothingTest4: {
// 		some Person0, Person1, Person2 : Person | {
// 			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
// 			next = Person0 -> Person1 + Person1 -> Person2


// 			//pre
// 			Ballpark.people = Person0 + Person1
// 			no waitingRoom.people
// 			no vacRoom.people
// 			no obsRoom.people

// 			NextPersonTracker.nextPerson = Person2
// 			Clock.timer = sing[0]
// 			vacRoom.numVaccines = sing[6]
// 			vacRoom.productionStage = sing[2]

// 			//post
// 			Ballpark.people = Person0 + Person1
// 			no waitingRoom.people
// 			no vacRoom.people'
// 			no obsRoom.people'

// 			NextPersonTracker.nextPerson' = Person2
// 			Clock.timer' = sing[1]
// 			vacRoom.numVaccines' = sing[5]
// 			vacRoom.productionStage = sing[3]

// 			doNothing
// 		}
// 	} is unsat 

// 	doNothingTest5: {
// 		some Person0, Person1, Person2 : Person | {
// 			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
// 			next = Person0 -> Person1 + Person1 -> Person2


// 			//pre
// 			Ballpark.people = Person0 + Person1
// 			no waitingRoom.people
// 			no vacRoom.people
// 			no obsRoom.people

// 			NextPersonTracker.nextPerson = Person2
// 			Clock.timer = sing[0]
// 			vacRoom.numVaccines = sing[0]
// 			vacRoom.productionStage = sing[1]

// 			//post
// 			Ballpark.people = Person0 + Person1
// 			no waitingRoom.people
// 			no vacRoom.people'
// 			no obsRoom.people'

// 			NextPersonTracker.nextPerson' = Person2
// 			Clock.timer' = sing[1]
// 			vacRoom.numVaccines' = sing[6]
// 			vacRoom.productionStage = sing[0]

// 			doNothing
// 		}
// 	} is sat 
// }	

// AK
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
	vacRoom.productionStage' = vacRoom.productionStage
}

// AK
pred ballToWaitingGuard{
	// waiting room must have room
	#(waitingRoom.people) < sum[waitingRoom.capacity]
	some p: Person | { p in Ballpark.people }
}

// AK
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

// QC

pred waitingToVacGuard{
	// vaccination room must have room
	#(vacRoom.people) < sum[vacRoom.capacity]
	sum[vacRoom.numVaccines] > 0
	some p: Person | { p in waitingRoom.people }
}

test expect{
	waitingToVacGuardTest1: {
			some Person0, Person1, Person2: Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				no Ballpark.people
				waitingRoom.people = Person0 + Person1
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[0]

				waitingToVacGuard
			}
	} is unsat 

	waitingToVacGuardTest2: {
		some Person0, Person1, Person2: Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2


			//pre
			Ballpark.people = Person0 + Person1
			no waitingRoom.people 
			no vacRoom.people
			no obsRoom.people

			NextPersonTracker.nextPerson = Person2
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[6]

			waitingToVacGuard
		}
	} is unsat 

	waitingToVacGuardTest3: {
		some Person0, Person1, Person2: Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2


			//pre
			no Ballpark.people 
			waitingRoom.people = Person2
			vacRoom.people = Person0 + Person1
			no obsRoom.people

			NextPersonTracker.nextPerson = Person2
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[6]

			waitingToVacGuard
		}
	} is unsat 

	waitingToVacGuardTest4: {
		some Person0, Person1, Person2: Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2


			//pre
			no Ballpark.people 
			waitingRoom.people = Person2
			vacRoom.people = Person1
			obsRoom.people = Person0 

			NextPersonTracker.nextPerson = Person2
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[1]

			waitingToVacGuard
		}
	} is sat 
}

// QC
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


test expect{
	waitingToVacTest1: {waitingToVac and not waitingToVacGuard} is unsat
	waitingToVacTest2: {eventually waitingToVac} is sat
	waitingToVacTest3: {
		some Person0, Person1, Person2: Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2


			//pre
			no Ballpark.people 
			waitingRoom.people = Person2
			vacRoom.people = Person1
			obsRoom.people = Person0 

			NextPersonTracker.nextPerson = Person2
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[1]

			waitingToVac
		}
	} is sat 

	waitingToVacTest4: {
		some Person0, Person1, Person2: Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2


			//pre
			no Ballpark.people 
			waitingRoom.people = Person2
			vacRoom.people = Person1
			obsRoom.people = Person0 

			NextPersonTracker.nextPerson = Person2
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[1]
			vacRoom.numVaccines' = sing[1]

			waitingToVac
		}
	} is unsat 

	waitingToVacTest4: {
		some Person0, Person1, Person2: Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2


			//pre
			no Ballpark.people 
			waitingRoom.people = Person2
			vacRoom.people = Person1
			obsRoom.people = Person0 

			NextPersonTracker.nextPerson = Person2
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[1]

			vacRoom.people' = Person1
			vacRoom.numVaccines' = sing[0]

			waitingToVac
		}
	} is unsat 
}


// YR
pred vacToObsGuard{
	before doNothing
	#(obsRoom.people) < sum[obsRoom.capacity]
}

// YR
pred vacToObs{
	// now we assume that vaccine takes one cycle (same time as doNothing) to be shot, and people can only come in at the beginning of the cycle

	vacToObsGuard
	vacRoom.numVaccines' = vacRoom.numVaccines
	people' = people - vacRoom->Person + obsRoom->(vacRoom.people)
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	Clock.timer' = Clock.timer
	vacRoom.productionStage = vacRoom.productionStage'
}

// SM
pred obsToExitGuard{
	some p: Person | {
		p in obsRoom.people
		before once (doNothing and before once (doNothing and before once (doNothing and before once (doNothing and p in obsRoom.people))))
	}
}

// SM
pred obsToExit{
	obsToExitGuard

	// once (doNothing and once(doNothing and once (doNothing and once p in obsRoom))) then move p to exit
	some p: Person | {
		p in obsRoom.people
		before once (doNothing and before once (doNothing and before once (doNothing and before once (doNothing and p in obsRoom.people))))
		people' = people - obsRoom->p
	}

	vacRoom.numVaccines' = vacRoom.numVaccines
	Clock.timer' = Clock.timer
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
	vacRoom.productionStage = vacRoom.productionStage'
}

// YR
pred makeVacGuard {
	#waitingRoom.people > sum[vacRoom.numVaccines]
	vacRoom.productionStage = sing[0] // no vaccine is getting made
}

// YR
pred makeVaccines {
	// max 6 every 3 states
	// similar to requests on elevator

	makeVacGuard

	vacRoom.productionStage' = sing[3]
	// vacRoom.numVaccines' = sing[sum[vacRoom.numVaccines, sing[6]]]
	people' = people
	Clock.timer' = Clock.timer
	NextPersonTracker.nextPerson' = NextPersonTracker.nextPerson
}

// QC
pred doNothingGuard{
	not ballToWaitingGuard
	not waitingToVacGuard
	not vacToObsGuard
	not obsToExitGuard
	not makeVacGuard
	// (#(vacRoom.people) = 2) or (some (vacRoom.people + obsRoom.people) and no (waitingRoom.people + Ballpark.people)) or (vacRoom.numVaccines = sing[0])
}


test expect {
	doNothingGuardTest1: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				doNothingGuard
			}
	} for exactly 3 Person is unsat 

	doNothingGuardTest2: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			no Ballpark.people 
			waitingRoom.people = Person2
			vacRoom.people = Person1 
			no obsRoom.people

			no NextPersonTracker.nextPerson
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[6]

			after {
				no Ballpark.people 
				no waitingRoom.people
				vacRoom.people = Person1 + Person2
				no obsRoom.people

				no NextPersonTracker.nextPerson
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]
			}
			after doNothingGuard
		}
	} for exactly 3 Person is sat 
	
	doNothingGuardTest3: {
		some Person0, Person1, Person2 : Person | eventually {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			no Ballpark.people
			no waitingRoom.people
			vacRoom.people =  Person0 + Person1
			no obsRoom.people

			NextPersonTracker.nextPerson = Person2
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[6]

			doNothingGuard
		}
	} for exactly 3 Person is sat 

		doNothingGuardTest3: {
		some Person0, Person1, Person2 : Person | eventually not {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			no Ballpark.people
			no waitingRoom.people
			vacRoom.people =  Person0 + Person1
			no obsRoom.people

			NextPersonTracker.nextPerson = Person2
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[6]

			doNothingGuard
		}
	} for exactly 3 Person is sat 
}

pred traces{
	// run everything
	
	// init
	// addToBallpark
	// after ballToWaiting
	// after after ballToWaiting
	// after after after waitingToVac
	// after after after after waitingToVac
	// after after after after after doNothing
	// after after after after after after vacToObs
	// after after after after after after after doNothing
	// after after after after after after after after doNothing
	// after after after after after after after after after doNothing
	// after after after after after after after after after after doNothing
	// after after after after after after after after after after after obsToExit
	// after after after after after after after after after after after after obsToExit
	// after after after after after after after after after after after after after doNothing

	init
	always (addToBallpark or ballToWaiting or waitingToVac or vacToObs or obsToExit or (doNothing and doNothingGuard))
}

// test expect{
// 	ISSAT: {
// 		always (addToBallpark or ballToWaiting or waitingToVac or vacToObs or obsToExit or (doNothing and doNothingGuard))
// 	} for 10 Person is sat
// }
//run {traces} for exactly 10 Person, 7 Int