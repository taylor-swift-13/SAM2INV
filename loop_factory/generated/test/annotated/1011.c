int main1(){
  int ms, p, gm2, mn, e6, fli;
  ms=1;
  p=0;
  gm2=28;
  mn=0;
  e6=1;
  fli=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e6 == p + 1;
  loop invariant gm2 + mn == 28;
  loop invariant 0 <= p <= ms;
  loop invariant mn >= 0;
  loop invariant fli <= e6;
  loop invariant gm2 >= 0;
  loop assigns fli, mn, e6, gm2, p;
*/
for (; gm2>0&&p<ms; p++) {
      if (gm2<=e6) {
          fli = gm2;
      }
      else {
          fli = e6;
      }
      mn = mn + fli;
      e6 += 1;
      gm2 = gm2 - fli;
  }
}