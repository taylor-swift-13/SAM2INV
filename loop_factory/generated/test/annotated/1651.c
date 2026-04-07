int main1(int f){
  int bg, gw, d8, p56;
  bg=f+24;
  gw=0;
  d8=0;
  p56=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= gw;
  loop invariant gw <= 4;
  loop invariant p56 == 4 - gw;
  loop invariant d8 == 4*gw - (gw*(gw - 1))/2;
  loop invariant bg == f + 24;
  loop invariant bg == \at(f,Pre) + 24;
  loop assigns d8, gw, p56;
*/
while (1) {
      if (!(gw<bg&&p56>0)) {
          break;
      }
      d8 = d8 + p56;
      gw = gw + 1;
      p56--;
  }
}