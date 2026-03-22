int main1(){
  int b, bx, pa, dp, xv2g;
  b=1+11;
  bx=3;
  pa=b;
  dp=0;
  xv2g=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= bx);
  loop invariant (bx <= b);
  loop invariant dp >= 0;
  loop invariant pa >= 12;
  loop invariant (bx == b) || (bx == 3);
  loop assigns dp, pa, bx;
*/
while (bx<=b-1) {
      dp = dp + pa;
      pa += bx;
      bx = b;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= bx);
  loop invariant (bx <= b);
  loop invariant pa >= 0;
  loop invariant xv2g >= 0;
  loop assigns xv2g, pa, bx;
*/
while (1) {
      if (!(bx>0)) {
          break;
      }
      xv2g = xv2g + pa;
      pa = pa + xv2g;
      bx = 0;
  }
}