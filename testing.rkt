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
<<<<<<< HEAD
// option max_tracelength 200
// option max_tracelength 20
option max_tracelength 6
=======
option max_tracelength 20
>>>>>>> 03faa293447c634880f3b0741fe04e09ef452a6f

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

pred vacToObsGuard{
	some vacRoom.people
	all p: vacRoom.people | {
		before once (doNothing and p in vacRoom.people)
	}
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

pred traces{
	// run everything

	init
	always (addToBallpark or ballToWaiting or waitingToVac or vacToObs or obsToExit or (doNothing and doNothingGuard))
}


// ======================================================
//               	  Hardcoded Trace
//
//  This is a hardcoded trace, which is able to run in time.
//  This follows the journey of 2 people through the site.
//  working. Check it out yourself (with the visualizer, viz.js)
//  by uncommenting traces_hard and the run statement below it.
// ======================================================
/*
pred traces_hard {
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
}

run {traces_hard} for exactly 10 Person, 7 Int
*/


// IGNORE THIS *******
// test expect{
// 	ISSAT: {
// 		init
// 		addToBallpark
// 		after ballToWaiting
// 		after after ballToWaiting
// 		after after after ballToWaiting
// 		after after after after ballToWaiting
// 		after after after after after waitingToVac
// 		after after after after after after waitingToVac
// 		after after after after after after after ballToWaiting
// 		after after after after after after after after ballToWaiting
// 		after after after after after after after after after doNothing
// 		// after after after after after after after after after doNothing
// 		// after after after after after after after after after after doNothing
// 		// after after after after after after after after after after after obsToExit
// 		// after after after after after after after after after after after after obsToExit
// 	} for 6 Person is sat
// }

// test expect{
// 	ISSAT: {
// 		always (addToBallpark or ballToWaiting or waitingToVac or vacToObs or obsToExit or (doNothing and doNothingGuard))
// 	} for 10 Person is sat
// }

// run {traces} for exactly 10 Person, 7 Int


// ======================================================
//               TESTING IMPORTANT NOTE
//
//  The length of these tests are long. We have a lot
//  of tests- 2700 lines of them. To ensure you are actually
//  able to run them, make sure max_tracelength is 6 (else 
//  you will encounter pardinus cli shutdown errors). We 
//  also recommend running them in chunks; commenting out
//  a few and running tests for 3-4 predicates at a time.
//  However, running them all at once will work.
//
// ======================================================

// ======================================================
//                  initCapacity Tests
// ======================================================
test expect {
	initCapacity1: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]


				//post
				Ballpark.people' = Person1
				waitingRoom.people' = Person0
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

                                initCapacity
    
			}
	} is sat

    initCapacity2 : {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				no Ballpark.people
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person0
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]

				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person1
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

                //post2
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				no obsRoom.people''

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[0]
				vacRoom.numVaccines'' = vacRoom.numVaccines'
				vacRoom.productionStage'' = vacRoom.productionStage'
    
                                initCapacity
                
			}
	} is sat

        //negative tests
        //9 capacity at ballpark
	initCapacityNeg1: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[9] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]


				//post
				Ballpark.people' = Person1
				waitingRoom.people' = Person0
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

                                initCapacity
    
			}
	} is unsat
    //3 capacity at vaccine room
    initCapacityNeg2 : {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[3] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				no Ballpark.people
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person0
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]

				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person1
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

                //post2
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				no obsRoom.people''

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[0]
				vacRoom.numVaccines'' = vacRoom.numVaccines'
				vacRoom.productionStage'' = vacRoom.productionStage'
    
                                initCapacity
                
			}
	} is unsat 
}

// ======================================================
//                  init Tests
// ======================================================
test expect {
        init0: {init} for 5 Person is sat

 
	init1: {
     
			some Person0, Person1, Person2, Person3, Person4  : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2 + Person2 -> Person3 + Person3 -> Person4


				//pre
				Ballpark.people = Person0 + Person1 + Person2 + Person3 + Person4
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = none
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]
                                vacRoom.productionStage = sing[0]

                                init               
    
			}
	} for 5 Person is sat

	init2: {
     
			some Person0, Person1, Person2, Person3, Person4  : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2 + Person2 -> Person3 + Person3 -> Person4


				//pre
				Ballpark.people = Person0 + Person1 + Person2 + Person3 + Person4
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = none
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]
                                vacRoom.productionStage = sing[0]

                                
 				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person1
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

                //post2
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				no obsRoom.people''

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[0]
				vacRoom.numVaccines'' = vacRoom.numVaccines'
				vacRoom.productionStage'' = vacRoom.productionStage'

                                init
    
			}
	} for 5 Person is sat
 
        //only four people
	initNeg1: {
     
			some Person0, Person1, Person2, Person3  : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2 + Person2 -> Person3 


				//pre
				Ballpark.people = Person0 + Person1 + Person2 + Person3
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = none
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]
                                vacRoom.productionStage = sing[0]

                                init               
    
			}
	} for 5 Person is unsat
        //not all in the ballpark to start
	initNeg2: {
     
			some Person0, Person1, Person2, Person3, Person4  : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2 + Person2 -> Person3 + Person3 -> Person4


				//pre
				Ballpark.people = Person0 + Person1 + Person2 + Person3
				waitingRoom.people = Person4
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = none
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]
                                vacRoom.productionStage = sing[0]

                                
 				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person1
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

                //post2
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				no obsRoom.people''

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[0]
				vacRoom.numVaccines'' = vacRoom.numVaccines'
				vacRoom.productionStage'' = vacRoom.productionStage'

                                init
    
			}
	} for 5 Person is unsat
}


// ======================================================
//                  obsToExitGuard Tests
// ======================================================
test expect {
    obsToExitGuardSat: {after after after after after obsToExitGuard} is sat
    nonemptyObsRoom: {always {obsToExitGuard implies some obsRoom.people}} is theorem

    obsToExitGuard1: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				obsRoom.people = Person2

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				//post0
				Ballpark.people' = Person0 + Person1
				no waitingRoom.people'
				no vacRoom.people'
				obsRoom.people' = Person2

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[1]
				vacRoom.numVaccines' = sing[6]

				//post1
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				obsRoom.people'' = Person2

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[2]
				vacRoom.numVaccines'' = sing[6]

				//post2
				Ballpark.people''' = Person0 + Person1
				no waitingRoom.people'''
				no vacRoom.people'''
				obsRoom.people''' = Person2

				NextPersonTracker.nextPerson''' = Person2
				Clock.timer''' = sing[3]
				vacRoom.numVaccines''' = sing[6]

				//post3
				Ballpark.people'''' = Person0 + Person1
				no waitingRoom.people''''
				no vacRoom.people''''
				obsRoom.people'''' = Person2

				NextPersonTracker.nextPerson'''' = Person2
				Clock.timer'''' = sing[4]
				vacRoom.numVaccines'''' = sing[6]
                                
                                not obsToExitGuard
                                not after obsToExitGuard
                                not after after obsToExitGuard
                                not after after after obsToExitGuard
                                after after after after obsToExitGuard
                    }
	} is sat

    obsToExitGuardNeg1: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				obsRoom.people = Person2

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				//post0
				Ballpark.people' = Person0 + Person1
				no waitingRoom.people'
				no vacRoom.people'
				obsRoom.people' = Person2

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = sing[6]

                                
                                not obsToExitGuard
                                after obsToExitGuard
                    }
	} is unsat

     //empty obsRoom
     obsToExitGuardNeg2: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1 + Person2
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				//post0
				Ballpark.people' = Person0 + Person1
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = sing[6]

                                
                                not obsToExitGuard
                                after obsToExitGuard
                    }
	} is unsat
    //person1 moves forward
    
    obsToExitGuardNeg3: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				obsRoom.people = Person2

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				//post0
				Ballpark.people' = Person0
				waitingRoom.people' = Person1
				no vacRoom.people'
				obsRoom.people' = Person2

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = sing[6]

                                
                                not obsToExitGuard
                                after obsToExitGuard
                    }
	} is unsat
     //Person2 not in the obsRoom from early enough
     obsToExitGuardNeg4: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1 + Person2
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people 

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				//post0
				Ballpark.people' = Person0 + Person1
				no waitingRoom.people'
				no vacRoom.people'
				obsRoom.people' = Person2

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[1]
				vacRoom.numVaccines' = sing[6]

				//post1
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				obsRoom.people'' = Person2

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[2]
				vacRoom.numVaccines'' = sing[6]

				//post2
				Ballpark.people''' = Person0 + Person1
				no waitingRoom.people'''
				no vacRoom.people'''
				obsRoom.people''' = Person2

				NextPersonTracker.nextPerson''' = Person2
				Clock.timer''' = sing[3]
				vacRoom.numVaccines''' = sing[6]

				//post3
				Ballpark.people'''' = Person0 + Person1
				no waitingRoom.people''''
				no vacRoom.people''''
				obsRoom.people'''' = Person2

				NextPersonTracker.nextPerson'''' = Person2
				Clock.timer'''' = sing[4]
				vacRoom.numVaccines'''' = sing[6]
                                
                                not obsToExitGuard
                                not after obsToExitGuard
                                not after after obsToExitGuard
                                not after after after obsToExitGuard
                                after after after after obsToExitGuard
                    }
	} is unsat
}


// ======================================================
//                  obsToExit Tests
// ======================================================
test expect {
    obsToExit1: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				obsRoom.people = Person2

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				//post0
				Ballpark.people' = Person0 + Person1
				no waitingRoom.people'
				no vacRoom.people'
				obsRoom.people' = Person2

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[1]
				vacRoom.numVaccines' = sing[6]

				//post1
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				obsRoom.people'' = Person2

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[2]
				vacRoom.numVaccines'' = sing[6]

				//post2
				Ballpark.people''' = Person0 + Person1
				no waitingRoom.people'''
				no vacRoom.people'''
				obsRoom.people''' = Person2

				NextPersonTracker.nextPerson''' = Person2
				Clock.timer''' = sing[3]
				vacRoom.numVaccines''' = sing[6]

				//post3
				Ballpark.people'''' = Person0 + Person1
				no waitingRoom.people''''
				no vacRoom.people''''
				obsRoom.people'''' = Person2

				NextPersonTracker.nextPerson'''' = Person2
				Clock.timer'''' = sing[4]
				vacRoom.numVaccines'''' = sing[6]

				//post4
				Ballpark.people''''' = Person0 + Person1
				no waitingRoom.people'''''
				no vacRoom.people'''''
				no obsRoom.people'''''
    
				NextPersonTracker.nextPerson''''' = Person2
				Clock.timer''''' = sing[4]
				vacRoom.numVaccines''''' = sing[6]
                                
                                not obsToExit
                                not after obsToExit
                                not after after obsToExit
                                not after after after obsToExit
                                after after after after obsToExit
                                //after after after after after obsToExit
                    }
	} is sat
    //Person2 doesn't leave
    obsToExitNeg1: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				obsRoom.people = Person2

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				//post0
				Ballpark.people' = Person0 + Person1
				no waitingRoom.people'
				no vacRoom.people'
				obsRoom.people' = Person2

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[1]
				vacRoom.numVaccines' = sing[6]

				//post1
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				obsRoom.people'' = Person2

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[2]
				vacRoom.numVaccines'' = sing[6]

				//post2
				Ballpark.people''' = Person0 + Person1
				no waitingRoom.people'''
				no vacRoom.people'''
				obsRoom.people''' = Person2

				NextPersonTracker.nextPerson''' = Person2
				Clock.timer''' = sing[3]
				vacRoom.numVaccines''' = sing[6]

				//post3
				Ballpark.people'''' = Person0 + Person1
				no waitingRoom.people''''
				no vacRoom.people''''
				obsRoom.people'''' = Person2

				NextPersonTracker.nextPerson'''' = Person2
				Clock.timer'''' = sing[4]
				vacRoom.numVaccines'''' = sing[6]

				//post4
				Ballpark.people''''' = Person0 + Person1
				no waitingRoom.people'''''
				no vacRoom.people'''''
				obsRoom.people''''' = Person2
    
				NextPersonTracker.nextPerson''''' = Person2
				Clock.timer''''' = sing[4]
				vacRoom.numVaccines''''' = sing[6]
                                
                                not obsToExit
                                not after obsToExit
                                not after after obsToExit
                                not after after after obsToExit
                                after after after after obsToExit
                                //after after after after after obsToExit
                    }
	} is unsat
     //Person2 leaves too soon
     obsToExitNeg2: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				obsRoom.people = Person2

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				//post0
				Ballpark.people' = Person0 + Person1
				no waitingRoom.people'
				no vacRoom.people'
				obsRoom.people' = Person2

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[1]
				vacRoom.numVaccines' = sing[6]

				//post1
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				obsRoom.people'' = Person2

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[2]
				vacRoom.numVaccines'' = sing[6]

				//post2
				Ballpark.people''' = Person0 + Person1
				no waitingRoom.people'''
				no vacRoom.people'''
				obsRoom.people''' = Person2

				NextPersonTracker.nextPerson''' = Person2
				Clock.timer''' = sing[3]
				vacRoom.numVaccines''' = sing[6]

				//post3
				Ballpark.people'''' = Person0 + Person1
				no waitingRoom.people''''
				no vacRoom.people''''
				no obsRoom.people''''

				NextPersonTracker.nextPerson'''' = Person2
				Clock.timer'''' = sing[4]
				vacRoom.numVaccines'''' = sing[6]

				//post4
				Ballpark.people''''' = Person0 + Person1
				no waitingRoom.people'''''
				no vacRoom.people'''''
				no obsRoom.people'''''
    
				NextPersonTracker.nextPerson''''' = Person2
				Clock.timer''''' = sing[4]
				vacRoom.numVaccines''''' = sing[6]
                                
                                not obsToExit
                                not after obsToExit
                                not after after obsToExit
                                not after after after obsToExit
                                after after after after obsToExit
                                //after after after after after obsToExit
                    }
	} is unsat
    //leaving takes time
    obsToExitNeg3: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				obsRoom.people = Person2

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				//post0
				Ballpark.people' = Person0 + Person1
				no waitingRoom.people'
				no vacRoom.people'
				obsRoom.people' = Person2

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[1]
				vacRoom.numVaccines' = sing[6]

				//post1
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				obsRoom.people'' = Person2

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[2]
				vacRoom.numVaccines'' = sing[6]

				//post2
				Ballpark.people''' = Person0 + Person1
				no waitingRoom.people'''
				no vacRoom.people'''
				obsRoom.people''' = Person2

				NextPersonTracker.nextPerson''' = Person2
				Clock.timer''' = sing[3]
				vacRoom.numVaccines''' = sing[6]

				//post3
				Ballpark.people'''' = Person0 + Person1
				no waitingRoom.people''''
				no vacRoom.people''''
				obsRoom.people'''' = Person2

				NextPersonTracker.nextPerson'''' = Person2
				Clock.timer'''' = sing[4]
				vacRoom.numVaccines'''' = sing[6]

				//post4
				Ballpark.people''''' = Person0 + Person1
				no waitingRoom.people'''''
				no vacRoom.people'''''
				no obsRoom.people'''''
    
				NextPersonTracker.nextPerson''''' = Person2
				Clock.timer''''' = sing[5]
				vacRoom.numVaccines''''' = sing[6]
                                
                                not obsToExit
                                not after obsToExit
                                not after after obsToExit
                                not after after after obsToExit
                                after after after after obsToExit
                    }
	} is unsat
}


// Make sure max_trace_length is 6

// ======================================================
//                  isQueue Tests
// ======================================================
test expect {
    // valid 
    queueTest1: {
        some Person0, Person1, Person2 : Person | {
            capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
            next = Person0 -> Person1 + Person1 -> Person2

            isQueue
        } 
    }is sat 

    // empty is sat
    queueTest2: {
            no Person
            capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
            isQueue
        } is sat

    // one person is unsat (we need 2 to have a queue)
    queueTest3: {
        #(Person) = 1
        some Person0 : Person | {
            capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
            no next
            isQueue
        }
    } for 1 Person is sat

    // one with 2 nexts
    queueTest4: {
        some Person0, Person1, Person2 : Person | {
            capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
            Person1 != Person2
            next = Person0 -> Person1 + Person0 -> Person2
            isQueue
        }
    } for 3 Person is unsat

    // loop
    queueTest5: {
        some Person0, Person1, Person2 : Person | {
            capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
            Person0 != Person1
            Person0 != Person2

            Person1 != Person0
            Person1 != Person2

            Person2 != Person0
            Person2 != Person1

            next = Person0 -> Person1 + Person1 -> Person2 + Person2 -> Person0
            isQueue
        }
    } is unsat

    // long queue is valid
    queueTest6: {
        some Person0, Person1, Person2, Person3, Person4, Person5, Person6, Person7 : Person | {
            capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
            next = Person0 -> Person1 + Person1 -> Person2 + Person2 -> Person3 + Person3 -> Person4 + 
            Person4 -> Person5 + Person5 -> Person6 + Person6 -> Person7

            isQueue
        }
    } for 8 Person is sat

    // disconnected
    queueTest7: {
        some Person0, Person1, Person2, Person3 : Person | {
            capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
            Person0 != Person1
            Person0 != Person2
            Person0 != Person3

            Person1 != Person0
            Person1 != Person2
            Person1 != Person3

            Person2 != Person0
            Person2 != Person1
            Person2 != Person3

            Person3 != Person0
            Person3 != Person1
            Person3 != Person2

            next = Person0 -> Person1 + Person2 -> Person3
            isQueue
        }
    } for 4 Person is unsat
}


// ======================================================
//                  addToBallpark Tests
// ======================================================
test expect {
    // Valid test
	addToBallpark1 : {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				no Ballpark.people
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person0
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]


				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person1
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				addToBallpark
			}
	} is sat 

    //next doesn't shift accordingly
    addToBallpark2 : {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2
                Person0 != Person1

				//pre
				no Ballpark.people
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person0
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]


				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person0
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				addToBallpark
			}
	} is unsat 

    //nothing to track
    addToBallpark3 : {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				no Ballpark.people
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				no NextPersonTracker.nextPerson
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]


				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				no NextPersonTracker.nextPerson'
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				addToBallpark
			}
	} is unsat 

    //works when there's already people there
    addToBallpark4 : {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				no Ballpark.people
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				no NextPersonTracker.nextPerson
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]


				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				no NextPersonTracker.nextPerson'
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				addToBallpark
			}
	} is unsat 

    //nextPerson grabs wrong value
    addToBallpark5 : {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2
                Person1 != Person2
                Person0 != Person2
                Person0 != Person1

				//pre
				no Ballpark.people
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person0
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]


				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				addToBallpark
			}
	} is unsat 

    //this shouldn't take any time
    addToBallpark6 : {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				no Ballpark.people
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person0
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]


				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person1
				Clock.timer' = sing[1]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				addToBallpark
			}
	} is unsat 

    // multiple in a row
    addToBallpark7 : {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				no Ballpark.people
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person0
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]

				//post
				Ballpark.people' = Person0
				no waitingRoom.people'
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person1
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

                //post2
				Ballpark.people'' = Person0 + Person1
				no waitingRoom.people''
				no vacRoom.people''
				no obsRoom.people''

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[0]
				vacRoom.numVaccines'' = vacRoom.numVaccines'
				vacRoom.productionStage'' = vacRoom.productionStage'

				addToBallpark
                after addToBallpark
			}
	} is sat 
}

// ======================================================
//                  ballToWaitingGuard Tests
// ======================================================
test expect {
    // Valid test (empty waiting room)
	ballToWaitingGuardTest1: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

<<<<<<< HEAD
				ballToWaitingGuard
			}
	} is sat 

    // Waiting room over capacity (order doesn't matter here)
	ballToWaitingGuardTest2: {
			some Person0, Person1, Person2, Person3, Person4, Person5 : Person | {
				Ballpark.people = Person0
                waitingRoom.capacity = sing[1]
				waitingRoom.people = Person1 + Person2
				no vacRoom.people
				no obsRoom.people

                NextPersonTracker.nextPerson = Person0
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				ballToWaitingGuard
			}
	} for 3 Person is unsat // to make them distinct

    // // waiting room at capacity is also a problem
    ballToWaitingGuardTest3: {
			some Person0, Person1, Person2 : Person | {
                waitingRoom.capacity = sing[1]
                people = Ballpark -> Person0 + Ballpark-> Person1 + waitingRoom -> Person2
				no vacRoom.people
				no obsRoom.people

                NextPersonTracker.nextPerson = Person0
				Clock.timer = sing[0]
				vacRoom.numVaccines = sing[6]

				ballToWaitingGuard
			}
	} for 3 Person is unsat // to make them distinct

    // empty ballpark (this test is unsat, meaning it should never be called when the ballpark is empty)
	ballToWaitingGuardTest4: {
			some Person0, Person1, Person2, Person3, Person4, Person5 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]

				no Ballpark.people
				waitingRoom.people = Person0 + Person1 + Person2 + Person3 + Person4 + Person5
				no vacRoom.people
				no obsRoom.people

				ballToWaitingGuard
			}
	} is unsat 

    // nobody anywhere (invalid guard)
	ballToWaitingGuardTest5: {
        no Person
			//some Person0, Person1, Person2, Person3, Person4, Person5 : Person | {
        capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]

        no Ballpark.people
        no waitingRoom.people
        no vacRoom.people
        no obsRoom.people

        ballToWaitingGuard
		//	}
	} is unsat 

    // one person case
	ballToWaitingGuardTest6: {
			some Person0, Person1 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]

				Ballpark.people = Person0
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				ballToWaitingGuard
			}
	} is sat 
}

// ======================================================
//                  ballToWaiting Tests
// ======================================================
test expect {
	ballToWaitingTest1: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]


				//post
				Ballpark.people' = Person1
				waitingRoom.people' = Person0
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				ballToWaiting
			}
	} is sat 

    //nonempty other rooms
    ballToWaitingTest15: {
			some Person000, Person00, Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person000-> Person00 + Person00->Person0 + Person0 -> Person1 + Person1 -> Person2


				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				vacRoom.people = Person00
				obsRoom.people = Person000

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]


				//post
				Ballpark.people' = Person1
				waitingRoom.people' = Person0
				vacRoom.people' = Person00
				obsRoom.people' = Person000

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				ballToWaiting
			}
	} is sat 

	// Person from the end of the line moves-- not the front (unsat)
	ballToWaitingTest2: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1

				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]

				//post
				Ballpark.people' = Person0
				waitingRoom.people' = Person1
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				ballToWaiting
			}
	} is unsat 

    // Proper movement causes a vaccine change (unsat)
	ballToWaitingTest3: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]

				//post
				Ballpark.people' = Person1
				waitingRoom.people' = Person0
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = sing[5]
				vacRoom.productionStage' = vacRoom.productionStage

				ballToWaiting
			}
	} is unsat 

    // Proper movement causes clock to increment (unsat)
	ballToWaitingTest4: {
			some Person0, Person1, Person2 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines' = sing[6]

				//post
				Ballpark.people' = Person1
				waitingRoom.people' = Person0
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[1]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				ballToWaiting
			}
	} is unsat 

    // Starting off with a nonempty room and multiple movements
	ballToWaitingTest5: {
			some Person0, Person1, Person2, Person3 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				Ballpark.people = Person1 + Person2
				waitingRoom.people = Person0
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person2
				Clock.timer = sing[0]
				vacRoom.numVaccines = vacRoom.numVaccines
				vacRoom.productionStage = vacRoom.productionStage

                //post1
				Ballpark.people' = Person2
				waitingRoom.people' = Person0 + Person1
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines'
				vacRoom.productionStage' = vacRoom.productionStage'

                //post2
				no Ballpark.people''
				waitingRoom.people'' = Person0 + Person1 + Person2
				no vacRoom.people''
				no obsRoom.people''

				NextPersonTracker.nextPerson'' = Person2
				Clock.timer'' = sing[0]
				vacRoom.numVaccines'' = vacRoom.numVaccines
				vacRoom.productionStage'' = vacRoom.productionStage

				ballToWaiting
                after ballToWaiting
			}
	} is sat 


     // Cannot move with a full room - this is unsat 
     // (this wouldn't be called in the situation, rather, doNothing would be)
	ballToWaitingTest6: {
			some Person0, Person1, Person2, Person3, Person4 : Person | {
				capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
				next = Person0 -> Person1 + Person1 -> Person2

				//pre
				Ballpark.people = Person4
				waitingRoom.people = Person0 + Person1 + Person2 + Person3
				no vacRoom.people
				no obsRoom.people

				NextPersonTracker.nextPerson = Person4
				Clock.timer = sing[0]
				vacRoom.numVaccines = vacRoom.numVaccines
				vacRoom.productionStage = vacRoom.productionStage

                //post1
				Ballpark.people' = Person4
				waitingRoom.people' = Person0 + Person1 + Person2 + Person3
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person4
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.productionStage' = vacRoom.productionStage

				ballToWaiting
			}
	} is unsat 
}

// ======================================================
//                  waitingToVacGuard Tests
// ======================================================

test expect{
	waitingToVacGuardTest1: {
			some Person0, Person1, Person2: Person | {
				#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int is unsat 

	waitingToVacGuardTest2: {
		some Person0, Person1, Person2: Person | {
			#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int  is unsat 

	waitingToVacGuardTest3: {
		some Person0, Person1, Person2: Person | {
			#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int  is unsat 

	waitingToVacGuardTest4: {
		some Person0, Person1, Person2: Person | {
			#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int is sat 
}

<<<<<<< HEAD
//======================================================
//                 waitingToVac Tests
//======================================================
=======
// ======================================================
//                  waitingToVac Tests
// ======================================================
>>>>>>> 03faa293447c634880f3b0741fe04e09ef452a6f

test expect{
	waitingToVacTest1: {waitingToVac and not waitingToVacGuard} is unsat
	waitingToVacTest2: {eventually waitingToVac} is sat
	waitingToVacTest3: {
		some Person0, Person1, Person2: Person | {
			#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int is sat 

	waitingToVacTest4: {
		some Person0, Person1, Person2: Person | {
			#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int is unsat 

	waitingToVacTest4: {
		some Person0, Person1, Person2: Person | {
			#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int is unsat 
}

// ======================================================
//                  doNothingGuard Tests
// ======================================================
<<<<<<< HEAD
=======

>>>>>>> 03faa293447c634880f3b0741fe04e09ef452a6f

test expect {
	doNothingGuardTest1: {
			some Person0, Person1, Person2 : Person | {
				#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int is unsat 

	doNothingGuardTest2: {
		some Person0, Person1, Person2 : Person | {
			#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int is sat 
	
	doNothingGuardTest3: {
		some Person0, Person1, Person2 : Person | eventually {
			#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int is sat 

		doNothingGuardTest3: {
		some Person0, Person1, Person2 : Person | eventually not {
			#(Person0 + Person1 + Person2) = 3
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
	} for exactly 3 Person, 5 Int is sat 
}








// ======================================================
//                  doNothing Tests
// ======================================================


test expect {
	doNothingTest0: {doNothing} is sat

	doNothingTest1: {
			some Person0, Person1, Person2 : Person | {
				#(Person0 + Person1 + Person2) = 3
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
				vacRoom.productionStage = sing[0]


				//post
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[1]
				vacRoom.numVaccines' = vacRoom.numVaccines
				vacRoom.numVaccines = sing[6]
				vacRoom.productionStage = sing[0]

				doNothing
			}
	} for exactly 3 Person, 5 Int is sat 

	doNothingTest2: {
			some Person0, Person1, Person2 : Person | {
				#(Person0 + Person1 + Person2) = 3
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
				vacRoom.productionStage = sing[0]


				//post
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[0]
				vacRoom.numVaccines' = sing[6]
				vacRoom.productionStage = sing[0]

				doNothing
			}
	} for exactly 3 Person, 5 Int is unsat 

	doNothingTest3: {
			some Person0, Person1, Person2 : Person | {
				#(Person0 + Person1 + Person2) = 3
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
				vacRoom.productionStage = sing[0]

				//post
				Ballpark.people = Person0 + Person1
				no waitingRoom.people
				no vacRoom.people'
				no obsRoom.people'

				NextPersonTracker.nextPerson' = Person2
				Clock.timer' = sing[1]
				vacRoom.numVaccines' = sing[5]
				vacRoom.productionStage = sing[0]

				doNothing
			}
	} for exactly 3 Person, 5 Int is unsat 

	doNothingTest4: {
		some Person0, Person1, Person2 : Person | {
			#(Person0 + Person1 + Person2) = 3
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
			vacRoom.productionStage = sing[2]

			//post
			Ballpark.people = Person0 + Person1
			no waitingRoom.people
			no vacRoom.people'
			no obsRoom.people'

			NextPersonTracker.nextPerson' = Person2
			Clock.timer' = sing[1]
			vacRoom.numVaccines' = sing[5]
			vacRoom.productionStage = sing[3]

			doNothing
		}
	} for exactly 3 Person, 5 Int is unsat 

	doNothingTest5: {
		some Person0, Person1, Person2 : Person | {
			#(Person0 + Person1 + Person2) = 3
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2


			//pre
			Ballpark.people = Person0 + Person1
			no waitingRoom.people
			no vacRoom.people
			no obsRoom.people

			NextPersonTracker.nextPerson = Person2
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[0]
			vacRoom.productionStage = sing[1]

			//post
			Ballpark.people = Person0 + Person1
			no waitingRoom.people'
			no vacRoom.people'
			no obsRoom.people'

			NextPersonTracker.nextPerson' = Person2
			Clock.timer' = sing[1]
			vacRoom.numVaccines' = sing[6]
			vacRoom.productionStage' = sing[0]

			doNothing
		}
	} for exactly 3 Person, 5 Int is sat 
}	


// ======================================================
//                 vacToObsGuard tests
// ======================================================
//
test expect {
	// nobody in obsRoom
	vog1: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person1 + Person2
			no waitingRoom.people
			vacRoom.people = Person0
			no obsRoom.people
			Clock.timer = sing[0]

			//post
			Ballpark.people' = Person1 + Person2
			no waitingRoom.people'
			vacRoom.people' = Person0
			no obsRoom.people'
			Clock.timer' = sing[1]

			after vacToObsGuard
		}
	} is sat

	// obsRoom full
	vog2: {
		some Person0, Person1, Person2, Person3, Person4 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2 + Person2 -> Person3 + Person3 -> Person4

			//pre
			no Ballpark.people
			no waitingRoom.people
			no vacRoom.people
			obsRoom.people = Person0 + Person1 + Person2 + Person3 + Person4
			Clock.timer = sing[0]

			//post
			no Ballpark.people'
			no waitingRoom.people'
			no vacRoom.people'
			obsRoom.people' = Person0 + Person1 + Person2 + Person3 + Person4
			Clock.timer' = sing[1]

			after vacToObsGuard
		}
	} is unsat

	// obsRoom over capacity
	vog3: {
		some Person0, Person1, Person2, Person3, Person4, Person5 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2 + Person2 -> Person3 + Person3 -> Person4 + Person4 -> Person5

			//pre
			no Ballpark.people
			no waitingRoom.people
			no vacRoom.people
			obsRoom.people = Person0 + Person1 + Person2 + Person3 + Person4 + Person5
			Clock.timer = sing[0]

			//post
			no Ballpark.people'
			no waitingRoom.people'
			no vacRoom.people'
			obsRoom.people' = Person0 + Person1 + Person2 + Person3 + Person4 + Person5
			Clock.timer' = sing[1]

			after vacToObsGuard
		}
	} is unsat

	// nobody in vacRoom
	vog4: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person1 + Person2
			no waitingRoom.people
			no vacRoom.people
			no obsRoom.people
			Clock.timer = sing[0]

			//post
			Ballpark.people' = Person1 + Person2
			no waitingRoom.people'
			no vacRoom.people'
			no obsRoom.people'
			Clock.timer' = sing[1]

			after vacToObsGuard
		}
	} is unsat

	// clock didn't move
	vog5: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person1 + Person2
			no waitingRoom.people
			vacRoom.people = Person0
			no obsRoom.people
			Clock.timer = sing[0]

			//post
			Ballpark.people' = Person1 + Person2
			no waitingRoom.people'
			vacRoom.people' = Person0
			no obsRoom.people'
			Clock.timer' = sing[0]

			after vacToObsGuard
		}
	} is unsat

	// multiple people in vacRoom
	vog6: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person2
			no waitingRoom.people
			vacRoom.people = Person0 + Person1
			no obsRoom.people
			Clock.timer = sing[0]

			//post
			Ballpark.people' = Person2
			no waitingRoom.people'
			vacRoom.people' = Person0 + Person1
			no obsRoom.people'
			Clock.timer' = sing[1]

			after vacToObsGuard
		}
	} is sat
}

// ======================================================
//                 vacToObs tests
// ======================================================
//
//
test expect {
	vto0: {always {vacToObs implies some vacRoom.people}} is theorem

	// one person moves to obsRoom
	vto1: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person1 + Person2
			no waitingRoom.people
			vacRoom.people = Person0
			no obsRoom.people
			Clock.timer = sing[0]

			//getting the shot
			Ballpark.people' = Person1 + Person2
			no waitingRoom.people'
			vacRoom.people' = Person0
			no obsRoom.people'
			Clock.timer' = sing[1]

			//post
			Ballpark.people'' = Person1 + Person2
			no waitingRoom.people''
			no vacRoom.people''
			obsRoom.people'' = Person0
			Clock.timer'' = sing[1]

			after vacToObs
		}
	} is sat

	// two persons move to obsRoom
	vto2: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person2
			no waitingRoom.people
			vacRoom.people = Person0 + Person1
			no obsRoom.people
			Clock.timer = sing[0]

			//getting the shot
			Ballpark.people' = Person2
			no waitingRoom.people'
			vacRoom.people' = Person0 + Person1
			no obsRoom.people'
			Clock.timer' = sing[1]

			//post
			Ballpark.people'' = Person2
			no waitingRoom.people''
			no vacRoom.people''
			obsRoom.people'' = Person0 + Person1
			Clock.timer'' = sing[1]

			after vacToObs
		}
	} is sat

	// one person didn't wait
	vto3: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2
			Person1 != Person2
			Person2 != Person0

			//pre
			Ballpark.people = Person1 + Person2
			no waitingRoom.people
			vacRoom.people = Person0
			no obsRoom.people
			Clock.timer = sing[0]

			//getting the shot
			Ballpark.people' = Person2
			no waitingRoom.people'
			vacRoom.people' = Person0 + Person1
			no obsRoom.people'
			Clock.timer' = sing[1]

			//post
			Ballpark.people'' = Person2
			no waitingRoom.people''
			no vacRoom.people''
			obsRoom.people'' = Person0 + Person1
			Clock.timer'' = sing[1]

			after vacToObs
		}
	} for 3 Person is unsat

	// one person didn't move to obsRoom
	vto4: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person2
			no waitingRoom.people
			vacRoom.people = Person0 + Person1
			no obsRoom.people
			Clock.timer = sing[0]

			//getting the shot
			Ballpark.people' = Person2
			no waitingRoom.people'
			vacRoom.people' = Person0 + Person1
			no obsRoom.people'
			Clock.timer' = sing[1]

			//post
			Ballpark.people'' = Person2
			no waitingRoom.people''
			vacRoom.people'' = Person1
			obsRoom.people'' = Person0
			Clock.timer'' = sing[1]

			after vacToObs
		}
	} is unsat

	// vaccine number changed
	vto5: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person2
			no waitingRoom.people
			vacRoom.people = Person0 + Person1
			no obsRoom.people
			Clock.timer = sing[0]
			vacRoom.numVaccines = sing[6]

			//getting the shot
			Ballpark.people' = Person2
			no waitingRoom.people'
			vacRoom.people' = Person0 + Person1
			no obsRoom.people'
			Clock.timer' = sing[1]
			vacRoom.numVaccines' = sing[6]

			//post
			Ballpark.people'' = Person2
			no waitingRoom.people''
			no vacRoom.people''
			obsRoom.people'' = Person0 + Person1
			Clock.timer'' = sing[1]
			vacRoom.numVaccines'' = sing[4]

			after vacToObs
		}
	} is unsat
}

// ======================================================
//                 makeVacGuard tests
// ======================================================
//
//
test expect {
	mvg1: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2
			Person0 != Person1

			//pre
			no Ballpark.people
			waitingRoom.people = Person0 + Person1 + Person2
			no vacRoom.people
			no obsRoom.people

			vacRoom.numVaccines = sing[0]
			vacRoom.productionStage = sing[0]

			makeVacGuard
		}
	} is sat

	// still vaccine left
	mvg2: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2
			Person0 != Person1

			//pre
			no Ballpark.people
			waitingRoom.people = Person0 + Person1 + Person2
			no vacRoom.people
			no obsRoom.people

			vacRoom.numVaccines = sing[3]
			vacRoom.productionStage = sing[0]

			makeVacGuard
		}
	} is unsat

	// vaccine already being made
	mvg3: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2
			Person0 != Person1

			//pre
			no Ballpark.people
			waitingRoom.people = Person0 + Person1 + Person2
			no vacRoom.people
			no obsRoom.people

			vacRoom.numVaccines = sing[0]
			vacRoom.productionStage = sing[2]

			makeVacGuard
		}
	} is unsat
}

// ======================================================
//                 makeVaccines tests
// ======================================================
//
//
test expect {
	mv1: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person2
			no waitingRoom.people
			vacRoom.people = Person0 + Person1
			no obsRoom.people
			Clock.timer = sing[0]
			vacRoom.productionStage = sing[0]

			//post
			Ballpark.people' = Person2
			no waitingRoom.people'
			vacRoom.people' = Person0 + Person1
			no obsRoom.people'
			Clock.timer' = sing[0]
			vacRoom.productionStage' = sing[3]

			makeVaccines
		}
	} is sat

	// took time
	mv2: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person2
			no waitingRoom.people
			vacRoom.people = Person0 + Person1
			no obsRoom.people
			Clock.timer = sing[0]
			vacRoom.productionStage = sing[0]

			//post
			Ballpark.people' = Person2
			no waitingRoom.people'
			vacRoom.people' = Person0 + Person1
			no obsRoom.people'
			Clock.timer' = sing[1]
			vacRoom.productionStage' = sing[3]

			makeVaccines
		}
	} is unsat

	// set the wrong production stage
	mv3: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person2
			no waitingRoom.people
			vacRoom.people = Person0 + Person1
			no obsRoom.people
			Clock.timer = sing[0]
			vacRoom.productionStage = sing[0]

			//post
			Ballpark.people' = Person2
			no waitingRoom.people'
			vacRoom.people' = Person0 + Person1
			no obsRoom.people'
			Clock.timer' = sing[0]
			vacRoom.productionStage' = sing[1]

			makeVaccines
		}
	} is unsat

	// people moved
	mv4: {
		some Person0, Person1, Person2 : Person | {
			capacity = Ballpark -> sing[10] + waitingRoom -> sing[4] + vacRoom -> sing[2] + obsRoom -> sing[5]
			next = Person0 -> Person1 + Person1 -> Person2

			//pre
			Ballpark.people = Person2
			no waitingRoom.people
			vacRoom.people = Person0 + Person1
			no obsRoom.people
			Clock.timer = sing[0]
			vacRoom.productionStage = sing[0]

			//post
			no Ballpark.people'
			waitingRoom.people' = Person2
			vacRoom.people' = Person0 + Person1
			no obsRoom.people'
			Clock.timer' = sing[0]
			vacRoom.productionStage' = sing[3]

			makeVaccines
		}
	} is unsat
}

