int main1(){
  int ugs, ilc, fv8, m4a, gyme;
  ugs=68;
  ilc=1;
  fv8=0;
  m4a=0;
  gyme=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m4a == fv8*(fv8 + 1)/2;
  loop invariant gyme == 3*fv8;
  loop invariant 0 <= fv8;
  loop invariant ilc <= 2 * ugs;
  loop assigns fv8, ilc, m4a, gyme;
*/
while (1) {
      if (!(ilc<=ugs)) {
          break;
      }
      fv8 = fv8 + 1;
      ilc = 2*ilc;
      m4a += fv8;
      gyme = gyme + 3;
  }
}