int main1(){
  int xn, xjf, r, ix;
  xn=(1%33)+18;
  xjf=0;
  r=0;
  ix=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ix == 2 * xjf;
  loop invariant 0 <= xjf;
  loop invariant 0 <= r;
  loop invariant r <= xjf;
  loop invariant xjf <= xn;
  loop assigns ix, xjf, r;
*/
while (xjf<=xn-1) {
      if (ix<xn) {
          r = xjf;
      }
      ix += 2;
      xjf++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xjf <= ix + 5;
  loop invariant r >= 0;
  loop invariant xn >= 0;
  loop invariant 0 <= ix;
  loop invariant 0 <= xjf;
  loop assigns xn, xjf;
*/
while (ix+6<=xjf) {
      xn += r;
      xjf = (ix+6)-1;
  }
}