int main1(int r){
  int mw, jxa, j, yqp, xy, yk8, h;
  mw=48;
  jxa=-6;
  j=0;
  yqp=0;
  xy=0;
  yk8=5;
  h=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mw == 48;
  loop invariant yk8 == 5;
  loop invariant 0 <= j <= yk8;
  loop invariant 0 <= xy <= h;
  loop invariant 0 <= yqp <= h;
  loop invariant j == yqp - xy;
  loop invariant jxa <= mw;
  loop invariant h - jxa == 6;
  loop invariant r == \at(r, Pre) + h*(h+1)/2;
  loop invariant jxa >= -6;
  loop assigns h, j, jxa, r, xy, yqp;
*/
while (jxa<mw) {
      if (jxa%3==0) {
          if (j>0) {
              j -= 1;
              xy++;
          }
      }
      else {
          if (j<yk8) {
              j++;
              yqp++;
          }
      }
      h += 1;
      jxa += 1;
      r += h;
  }
}