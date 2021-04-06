/*
  Forge Visualization script                                                                 
*/

// this clears the svg that Sterling provides to us.
d3.select(svg).selectAll("*").remove();

const timers = Clock.atoms(true);
const vaccines = vacRoom.atoms(true);
const persons = Person.atoms(true);
const rooms = Room.atoms(true);

const RED = "#E54B4B";
const BLUE = "#0495c2";

const p1 = "https://www.linkpicture.com/q/imageedit_7_5723744859.png";
const p2 = "https://www.linkpicture.com/q/imageedit_5_4050192827.png";
const p3 = "https://www.linkpicture.com/q/imageedit_3_8921239886.png";
const p4 = "https://www.linkpicture.com/q/imageedit_1_6002236047.png";

function pic(d, i) {
  if (i%4 === 0) {
    return p1; 
  }
  if (i%4 === 1) {
    return p2; 
  }
  if (i%4 === 2) {
    return p3; 
  }
  if (i%4 === 3) {
    return p4; 
  }
}


d3.select(svg)
    .append('image')
    .attr('xlink:href', 'https://www.linkpicture.com/q/imageedit_9_5714665830.png')
    .attr("width", 1000)
    .attr("height", 650)
    .attr('x', -20)
    .attr('y', 0)


console.log(rooms);
//console.log(rooms.length);
let toRet = []

let d = "vacRoom0";
for(let i = 0; i < 4; i++) {
  let x = rooms[i].people._tuples
  if(d === rooms[i]._id) {
    // find the people in that room
  for(let j = 0; j < x.length; j++) {
      let y = x[j]._atoms;
      for(let k = 0; k < y.length; k++) {
        let p = y[0]._id;
        let loc = rooms[i]._id;
        toRet.push(y[0])
        //console.log(y)
      }    
    }
    drawPerson(toRet)


  }
}


function drawPerson(datas) {
  console.log("HERE!")
  d3.select(svg)
    .selectAll("people")
    .data(datas)
    .join("image")
    .attr('xlink:href', pic)
    .attr("width", 60)
    .attr("height", 60)
    .attr("x", 20)
    .attr("y", (d, i) => {
        return 200 + (i * 40);
    });
}

function findLoc(d, i) {
  
}


d3.select(svg)
    .selectAll("timerss")
    .data(timers)
    .join("text")
    .attr("font-weight", 800)
    .attr("x", 75)
    .attr("y", 75)
    .text((d, i) => {
        // this line uses js string variable interpolation
        return `Time: ${d.timer}`;
    });

d3.select(svg)
    .selectAll("vacciness")
    .data(vaccines)
    .join("text")
    .attr("x", 300)
    .attr("y", 405)
    .text((d, i) => {
        // this line uses js string variable interpolation
        return `Vaccines: ${d.numVaccines}`;
    });

/*
d3.select(svg)
    .selectAll("people")
    .data(persons)
    .join("image")
    .attr('xlink:href', pic)
    .attr("width", 60)
    .attr("heigh", 60)
    .attr("x", 20)
    .attr("y", (d, i) => {
        return 200 + (i * 20);
    });
    */
/*
// ballpark
d3.select(svg)              // select the svg 
    .append("rect")         // append a rectangle element to the selected element (the svg)
    .attr("x", 100)          // give the rect an x coordinate
    .attr("y", 100)          // give the rect a y coordinate
    .attr("width", 325)     // give the rect a width
    .attr("height", 120)    // give the rect a height
    .style("fill", BLUE)    // give the rect a fill color (RED is declared in line 15)
    .attr("stroke-width", 5)
	  .attr("fill-opacity","0.2")
    .style("stroke", RED);    // give the rect a fill color (RED is declared in line 15)

  
// waiting room
d3.select(svg)              // select the svg 
    .append("rect")         // append a rectangle element to the selected element (the svg)
    .attr("x", 100)          // give the rect an x coordinate
    .attr("y", 270)          // give the rect a y coordinate
    .attr("width", 300)     // give the rect a width
    .attr("height", 60)    // give the rect a height

// vaccination room
d3.select(svg)              // select the svg 
    .append("rect")         // append a rectangle element to the selected element (the svg)
    .attr("x", 100)          // give the rect an x coordinate
    .attr("y", 370)          // give the rect a y coordinate
    .attr("width", 150)     // give the rect a width
    .attr("height", 60)    // give the rect a height

// observation room
d3.select(svg)              // select the svg 
    .append("rect")         // append a rectangle element to the selected element (the svg)
    .attr("x", 100)          // give the rect an x coordinate
    .attr("y", 470)          // give the rect a y coordinate
    .attr("width", 375)     // give the rect a width
    .attr("height", 60)    // give the rect a height
*/
/*
d3.select(svg)
    .append('image')
    .attr('xlink:href', 'https://i.pinimg.com/originals/f8/01/e4/f801e4c0be2ef6505f099093a15ae2d8.jpg')
    .attr('width', 200)
    .attr('height', 200)
*/







