int main1(){
  int i0, i, pox, ivr, sglm, nm9;
  i0=48;
  i=0;
  pox=0;
  ivr=0;
  sglm=20;
  nm9=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nm9 == 5 + i0 * ivr;
  loop invariant pox == ivr;
  loop invariant 0 <= ivr;
  loop invariant ivr <= i0;
  loop assigns nm9, pox, sglm, ivr;
*/
while (1) {
      if (!(ivr<i0)) {
          break;
      }
      nm9 = nm9 + i0;
      pox++;
      sglm = sglm*2;
      ivr++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ivr;
  loop invariant nm9 == 5 + i0 * i0 + (ivr - i0);
  loop invariant i == (ivr - i0) * sglm;
  loop assigns nm9, ivr, i;
*/
while (ivr<=sglm-1) {
      nm9 = nm9 + 1;
      ivr++;
      i = i + sglm;
  }
}