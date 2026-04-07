int main1(){
  int w, dr1, mw2, qj;
  w=(1%27)+17;
  dr1=0;
  mw2=dr1;
  qj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dr1 == qj;
  loop invariant mw2 == dr1 * (dr1 + 1) * (2 * dr1 + 1) / 6;
  loop invariant dr1 <= w;
  loop invariant 0 <= qj;
  loop assigns dr1, mw2, qj;
*/
while (dr1 < w) {
      dr1 += 1;
      qj = qj + 1;
      mw2 = mw2 + qj * qj;
  }
}