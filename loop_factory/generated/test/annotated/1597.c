int main1(){
  int mr6, t7n0, irg, shi, xzmq, lem, on, r, bl2i;
  mr6=75;
  t7n0=0;
  irg=1;
  shi=1;
  xzmq=0;
  lem=7;
  on=0;
  r=4;
  bl2i=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= t7n0 <= mr6;
  loop invariant t7n0 == on;
  loop invariant lem == 7 + t7n0;
  loop invariant r == 4 + 6 * t7n0;
  loop invariant 0 <= irg <= lem;
  loop invariant 0 <= xzmq <= t7n0;
  loop invariant bl2i >= 1;
  loop invariant shi >= 1;
  loop invariant irg + xzmq == shi;
  loop assigns bl2i, irg, lem, on, r, shi, t7n0, xzmq;
*/
while (1) {
      if (!(t7n0<mr6)) {
          break;
      }
      if (t7n0%3==0) {
          if (irg>0) {
              irg -= 1;
              xzmq += 1;
          }
      }
      else {
          if (irg<lem) {
              irg++;
              shi = shi + 1;
          }
      }
      t7n0 += 1;
      bl2i += irg;
      on += 1;
      r += 2;
      lem = lem + 1;
      r += 4;
  }
}