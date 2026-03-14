int main1(int q,int j){
  int z8, mw, ua, p;
  z8=89;
  mw=0;
  ua=1;
  p=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= p <= z8;
  loop invariant ua == 1 + p * q;
  loop invariant mw == 0;
  loop invariant j == \at(j,Pre);
  loop invariant q == \at(q, Pre) + mw * p;
  loop invariant ua == 1 + p * \at(q,Pre);
  loop assigns p, ua, q;
*/
while (p<z8) {
      ua = ua + q;
      p++;
      q += mw;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p + mw == z8;
  loop invariant q + mw == \at(q,Pre);
  loop invariant 0 <= p <= z8;
  loop assigns p, q, mw;
*/
while (1) {
      if (!(p>0)) {
          break;
      }
      mw = mw + 1;
      q = q - 1;
      p -= 1;
  }
}