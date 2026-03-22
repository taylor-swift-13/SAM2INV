int main1(){
  int pfh, feg, f, ctw;
  pfh=(1%15)+17;
  feg=0;
  f=pfh;
  ctw=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ctw == feg;
  loop invariant (feg + f == pfh);
  loop invariant 0 <= feg <= pfh;
  loop assigns feg, ctw, f;
*/
while (1) {
      if (!(feg < pfh)) {
          break;
      }
      feg = feg + 1;
      ctw = feg;
      f = pfh - feg;
  }
}