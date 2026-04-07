int main1(){
  int iz, kc, pr, vp;
  iz=1;
  kc=0;
  pr=iz;
  vp=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pr == iz - kc;
  loop invariant (0 <= kc);
  loop invariant (kc <= iz);
  loop invariant vp == 5 + kc * iz;
  loop invariant iz == 1;
  loop assigns kc, vp, pr;
*/
while (kc < iz) {
      kc += 1;
      vp = vp + iz;
      pr = iz - kc;
  }
}