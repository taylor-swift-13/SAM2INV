int main1(int c,int i){
  int he, qa, jyx, y1v;
  he=29;
  qa=1;
  jyx=0;
  y1v=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jyx == (qa - 1) * (qa - 1);
  loop invariant y1v == 2 * qa - 6;
  loop invariant c == \at(c, Pre) + (qa * qa + qa - 2) / 2;
  loop invariant qa >= 1;
  loop invariant qa <= he + 1;
  loop assigns jyx, qa, y1v, c;
*/
while (qa<=he) {
      jyx = jyx+2*qa-1;
      qa = qa + 1;
      y1v += 2;
      c += qa;
  }
}