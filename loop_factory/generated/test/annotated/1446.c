int main1(){
  int vy9, dwo, r3, gv;
  vy9=1*5;
  dwo=0;
  r3=0;
  gv=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vy9 == 5;
  loop invariant dwo <= vy9;
  loop invariant r3 == 3*dwo - (dwo*(dwo - 1))/2;
  loop invariant dwo + gv == 3;
  loop invariant 0 <= dwo;
  loop assigns dwo, r3, gv;
*/
while (1) {
      if (!(dwo<vy9&&gv>0)) {
          break;
      }
      dwo = dwo + 1;
      r3 = r3 + gv;
      gv = gv - 1;
  }
}