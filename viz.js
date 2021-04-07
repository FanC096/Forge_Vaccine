/*
  Forge Visualization script                                                                 
*/

// this clears the svg that Sterling provides to us.
d3.select(svg).selectAll("*").remove();

const timers = Clock.atoms(true);
const vaccines = vacRoom.atoms(true);
const persons = Person.atoms(true);
const rooms = Room.atoms(true);
const nextRel = next;
let firstPerson = null;
let lastPerson = null;
let nextMap = {};

// First: Setup the nextMap to represent the ordered queue

// find the first atom in the queue
function findFirst(){
  let notFirst = []
  for(let j = 0; j < 9; j++) {
    notFirst.push(nextRel._tuples[j]._atoms[0].next._id)
  }

  for(let j = 0; j < 10; j++) {
    if(!notFirst.includes(persons[j]._id)){
      firstPerson = persons[j];
    }
    if(persons[j].next._tuples.length === 0) {
      lastPerson = persons[j];
    }
  }
}
findFirst();

// sets up the nextMap to represent the queue
function setupNext(p, i){
  //if(p.next == null)
  if(p._id == lastPerson._id) {
    return;
  }
  
  nextMap[p] = i;
  setupNext(p.next, i+1)
}
setupNext(firstPerson, 0);

const p1 = "https://www.linkpicture.com/q/imageedit_7_5723744859.png";
const p2 = "https://www.linkpicture.com/q/imageedit_5_4050192827.png";
const p3 = "https://www.linkpicture.com/q/imageedit_3_8921239886.png";
const p4 = "https://www.linkpicture.com/q/imageedit_1_6002236047.png";

// draw the background
d3.select(svg)
    .append('image')
    .attr('xlink:href', 'https://www.linkpicture.com/q/imageedit_9_5714665830.png')
    .attr("width", 1000)
    .attr("height", 650)
    .attr('x', -20)
    .attr('y', 0)

// function to select an image for a person
//let randVal = 0;
function pic(d, i) {
  let x = parseInt(d._id.slice(-1));
  
  if (x%4 === 0) {
    return p1; 
  }
  if (x%4 === 1) {
    return p2; 
  }
  if (x%4 === 2) {
    return p3; 
  }
  if (x%4 === 3) {
    return p4; 
  }
}

// helper function to calculate the x position of a person
function roomCoordsX(d, i) {
  if (d._id === "Ballpark0") {
    return ballParkCalculator(i, false); 
  }
  if (d._id === "waitingRoom0") {
    return waitingRoomCalculator(i, false);; 
  }
  if (d._id === "vacRoom0") {
    return 510 + 130 * i;
  }
  if (d._id === "obsRoom0") {
    return obsRoomCalculator(i, false); 
  }
}

// helper function to calculate the y position of a person
function roomCoordsY(d, i) {
  if (d._id === "Ballpark0") {
    return ballParkCalculator(i, true); 
  }
  if (d._id === "waitingRoom0") {
    return waitingRoomCalculator(i, true); 
  }
  if (d._id === "vacRoom0") {
    return 330;
  }
  if (d._id === "obsRoom0") {
    return obsRoomCalculator(i, true); 
  }
}

// helper function to calculate the positions of people in the ballPark
function ballParkCalculator(i, isY) {
  // column 1
  if(i <= 1){ 
    if(isY){
      return 150 + 75 * i;
    } else {
      return 410;
    }
  }
  
  //column 2
  if(i <= 4 && i > 1) {
    j = i - 2 //offset
    if(isY){
      return 225 - 75 * j;

    } else {
      return 355;
    }
  }
  
  //column 3
  if(i <= 7 && i > 4) {
    j = i - 5 //offset
    if(isY){
      return 75 + 75 * j;
    } else {
      return 300;
    }
  }
  
  //column 4
  if(i <= 9 && i > 7) {
    j = i - 8 //offset
    if(isY){
      return 150 + 75 * j;
    } else {
      return 250;
    }
  }
}
// helper function to calculate the positions of people in the waitingRoom
function waitingRoomCalculator(i, isY) {
  // column 1
  if(i <= 1){
    if(isY){
      return 230;
    } else {
      return 570 + 85 * i;
    }
  }
  //column 2
  if(i <= 3 && i > 1) {
    j = i - 2 //offset
    if(isY){
      return 165;
    } else {
      return 635 - 85 * j;
    }
  }
}

// helper function to calculate the positions of people in the obsRoom
function obsRoomCalculator(i, isY) {
    // column 1
  if(i <= 1){
    if(isY){
      return 515;
    } else {
      return 620 - 85 * i;
    }
  }
  
  if(i <= 4 && i > 1){
    j = i - 2
    if(isY){
      return 440;
    } else {
      return 650 - 75 * j;
    }
  }
  
}

// Helper function to put a group of people into queue-order
function shuffleIntoOrder(people) {
  let toRet = []
  let minVal = 100
  let minP = 100;
  let x = people.length
  
  while (people.length > 0) {
    minVal = 100
    // find the minimum index in the given
    for (let i = 0; i < people.length; i++) {
      // if the current person is higher in order than saved
        if(nextMap[people[i]] < minVal) {
            //current min 
            minVal = nextMap[people[i]];
            minP = i;
        }
    }
    
    toRet.push(people[minP])
    people.splice(minP, 1);
  }
  return toRet
}
  

// draw the people in a room
function drawRoom(d){
  let toRet = []
   for(let i = 0; i < 4; i++) {
    let x = rooms[i].people._tuples
    if(d._id === rooms[i]._id) {
        // find the people in that room
    for(let j = 0; j < x.length; j++) {
        let y = x[j]._atoms;
        for(let k = 0; k < y.length; k++) {
            let p = y[0]._id;
            toRet.push(y[0])
          }    
        }
        drawPerson(shuffleIntoOrder(toRet), rooms[i]);
    }
   }
  return toRet;
}

// draw the people based on their room
function drawPerson(data, roomName) {
  d3.select(svg)
    .selectAll("people")
    .data(data)
    .join("image")
    .attr('xlink:href', pic)
    .attr("x", ((d, i) => {
        // this line uses js string variable interpolation
        return roomCoordsX(roomName, i);
    }))
    .attr("y", ((d, i) => {
        // this line uses js string variable interpolation
        return roomCoordsY(roomName, i);
    }))
    .attr("width", 50)
    .attr("height", 50);
}


for (let i = 0; i < rooms.length; i++) {
    toRet = drawRoom(rooms[i]);
  }
    
// draw the timers
d3.select(svg)
    .selectAll("timerss")
    .data(timers)
    .join("text")
    .attr("font-weight", 800)
    .attr("x", 75)
    .attr("y", 75)
    .style("font-size", "21px")
    .text((d, i) => {
        // this line uses js string variable interpolation
        return `Time: ${d.timer._id}`;
    });


// draw the vaccines
d3.select(svg)
    .selectAll("vacciness")
    .data(vaccines)
    .join("text")
    .attr("x", 315)
    .attr("y", 365)
    .style("font-size", "18px")
    .attr("font-weight", 800)
    .text((d, i) => {
        // this line uses js string variable interpolation
        return `Vaccines: ${d.numVaccines._id}`;
    });

// ballpark dividers
d3.select(svg)              // select the svg 
    .append("rect")         // append a rectangle element to the selected element (the svg)
    .attr("x", 300)          // give the rect an x coordinate
    .attr("y", 57)          // give the rect a y coordinate
    .attr("width", 2)     // give the rect a width
    .attr("height", 180)    // give the rect a height

d3.select(svg)              // select the svg 
    .append("rect")         // append a rectangle element to the selected element (the svg)
    .attr("x", 407)          // give the rect an x coordinate
    .attr("y", 57)          // give the rect a y coordinate
    .attr("width", 2)     // give the rect a width
    .attr("height", 180)    // give the rect a height

d3.select(svg)              // select the svg 
    .append("rect")         // append a rectangle element to the selected element (the svg)
    .attr("x", 352)          // give the rect an x coordinate
    .attr("y", 108)          // give the rect a y coordinate
    .attr("width", 2)     // give the rect a width
    .attr("height", 180)    // give the rect a height


// waitingRoom dividers
d3.select(svg)              // select the svg 
    .append("rect")         // append a rectangle element to the selected element (the svg)
    .attr("x", 477)          // give the rect an x coordinate
    .attr("y", 220)          // give the rect a y coordinate
    .attr("width", 180)     // give the rect a width
    .attr("height", 2) 







