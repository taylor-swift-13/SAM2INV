int main1(){
  int jtw, z3kb, j, fv, mfup, c;
  jtw=1+3;
  z3kb=1;
  j=0;
  fv=jtw;
  mfup=5;
  c=z3kb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= j && j <= jtw);
  loop invariant mfup == 5 + 6*j - (j*(j+1))/2;
  loop invariant c == 1;
  loop invariant j + fv == jtw;
  loop invariant mfup == 5 + j*(jtw - 1 + 2*c) - j*(j - 1)/2;
  loop assigns fv, j, mfup;
*/
while (j<jtw&&fv>0) {
      fv -= 1;
      j++;
      mfup += fv;
      mfup = mfup+c+c;
  }
/*@
  assert (jtw == 4) &&
         (c == 1) &&
         (j == 4) &&
         (fv == 0) &&
         (mfup == 19);
*/
}
