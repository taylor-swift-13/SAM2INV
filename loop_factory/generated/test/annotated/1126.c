int main1(){
  int d0, c9, uxv, x, cgv, d;
  d0=1+19;
  c9=d0;
  uxv=(1%40)+2;
  x=0;
  cgv=-6;
  d=c9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d + uxv == 23;
  loop invariant uxv > 0;
  loop invariant x >= 0;
  loop invariant d > 0;
  loop assigns x, uxv, d;
*/
while (uxv!=x) {
      x = uxv;
      uxv = (uxv+d0/uxv)/2;
      d = d+x-uxv;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d0 == 1 + 19;
  loop invariant cgv == -6;
  loop invariant uxv >= 0;
  loop invariant d >= 0;
  loop invariant c9 > 0;
  loop invariant c9 <= 40;
  loop assigns uxv, d, c9;
*/
while (1) {
      if (!(c9*2<=cgv)) {
          break;
      }
      uxv += d;
      d += d;
      c9 = c9*2;
  }
}