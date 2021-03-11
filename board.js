function setup() {
  createCanvas(500, 500);
}

function regular(n, len=100)
{
  push();
  angle = TWO_PI / n;
  beginShape();
  x = 0;
  y = 0;
  for (a=0; a<TWO_PI; a+=angle) {
    x += cos(a) * len;
    y += sin(a) * len;
    vertex(x, y);
  }
  endShape(CLOSE);
  pop();
}

function tri(len=100) {regular(3,len);}

function boardtri(len=200)
{
  push();

  line(0,0,len,0);
  translate(len,0);
  rotate(PI/1.5);

  fill(255);
  rect(0,-5,len/2,5);
  fill(0);
  rect(len/2,-5,len/2,5);

  translate(len,0);
  rotate(PI/1.5);

  line(0,0,len,0);

  pop();
}

function board(len=200) 
{
  push();
  stroke(120,0,0);
  for (i=0; i<6; i++) {
      rotate(PI/3);
      boardtri(len);
  }
  pop();
}

function panel(bw=0, rot=0, len=200)
{
  push();
  for (i=0; i<rot; i++) {
  translate(200,0);
  rotate(TWO_PI*2/6);
  }
  
  push();
  strokeWeight(0);
  if(bw) {fill(0);} else {fill(255);}
  tri(len/2);
  if(!bw) {fill(0);} else {fill(255);}
  translate(len/2,0);
  tri();
  rotate(TWO_PI/6);
  tri();
  translate(len/2,0)
  rotate(TWO_PI/6);
  tri();
  pop();

  pop();  
}

function panels(arr)
{
  push();
  arr.forEach(p => {if (p != 0) {panel(p % 2, p % 3);} rotate(TWO_PI/6);});
  pop();
}

function draw() {
  translate(width/2, height/2);
  background(100,150,0);
  fill(255,0,0);
  panels([1,0,3,0,6,7]);
  board();
}
