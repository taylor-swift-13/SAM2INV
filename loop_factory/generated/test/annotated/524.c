int main1(int r){
  int xv, y8a, tf, xwq;
  xv=r+11;
  y8a=1;
  tf=0;
  xwq=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r - xwq == \at(r, Pre);
  loop invariant tf == xwq * r - (xwq * (xwq + 1)) / 2;
  loop invariant xv == \at(r, Pre) + 11;
  loop invariant r == \at(r,Pre) + xwq * y8a;
  loop invariant tf == \at(r,Pre) * xwq + y8a * xwq * (xwq - 1) / 2;
  loop invariant xwq >= 0;
  loop assigns xwq, tf, r;
*/
while (1) {
      if (!(xwq<xv)) {
          break;
      }
      xwq++;
      tf += r;
      r += y8a;
  }
}