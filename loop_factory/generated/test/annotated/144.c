int main1(){
  int mmp, kc, p8v, j0b;
  mmp=1+22;
  kc=0;
  p8v=3;
  j0b=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p8v == 3 + 4*kc;
  loop invariant 0 <= kc;
  loop invariant kc <= mmp;
  loop invariant j0b == 7 + 4*kc;
  loop invariant mmp == 23;
  loop assigns kc, p8v, j0b;
*/
while (1) {
      if (!(kc<mmp)) {
          break;
      }
      kc += 1;
      p8v += 4;
      j0b += 4;
  }
}