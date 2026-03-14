int main1(){
  int t1i, cp, dfq, k, fa;
  t1i=1+25;
  cp=0;
  dfq=4;
  k=0;
  fa=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= k <= t1i;
  loop invariant dfq == k + 4;
  loop assigns k, dfq;
*/
while (1) {
      if (!(k<t1i)) {
          break;
      }
      k += 1;
      dfq = dfq + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cp == fa - 1;
  loop invariant fa <= dfq;
  loop invariant 0 <= cp;
  loop assigns cp, fa;
*/
while (1) {
      if (!(fa<dfq)) {
          break;
      }
      cp++;
      fa++;
  }
}