int main1(){
  int h, wk, ve, wku;
  h=1*2;
  wk=0;
  ve=0;
  wku=h;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ve <= h;
  loop invariant 0 <= wku <= 2*h;
  loop invariant wk == 0;
  loop invariant h == 2;
  loop invariant (ve == 0) ==> (wku == h);
  loop invariant ((ve > 0) && (ve <= h)) ==> (wku == 2*(h - ve));
  loop assigns ve, wku;
*/
while (1) {
      if (!(ve<h)) {
          break;
      }
      ve = ve + 1;
      wku = (h)+(-(ve));
      if (wk+2<=wk+h) {
          wku = wku + wku;
      }
  }
}