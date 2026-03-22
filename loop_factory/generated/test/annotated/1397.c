int main1(int j){
  int gs, s, e4k, a, mfik, zjq, tzy;
  gs=j*2;
  s=0;
  e4k=s;
  a=11;
  mfik=s;
  zjq=0;
  tzy=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mfik == 6 * zjq;
  loop invariant tzy >= 7;
  loop invariant mfik >= 0;
  loop invariant gs == 2 * j;
  loop invariant tzy >= 2 * e4k;
  loop invariant a == 3*zjq*zjq - 3*zjq + 11;
  loop invariant e4k == zjq*zjq*zjq - 3*zjq*zjq + 13*zjq;
  loop invariant gs == 2 * \at(j, Pre);
  loop assigns e4k, a, zjq, tzy, mfik;
*/
while (zjq<=gs) {
      e4k = e4k + a;
      a = a + mfik;
      zjq += 1;
      tzy += e4k;
      mfik += 6;
      tzy = tzy*2;
  }
}