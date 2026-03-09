int main1(){
  int ykpi, pj, n, up;
  ykpi=18;
  pj=3;
  n=ykpi;
  up=ykpi;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (up == ykpi);
  loop invariant n == ykpi + up*(pj - 3);
  loop invariant 3 <= pj <= ykpi;
  loop assigns n, pj;
*/
while (1) {
      if (!(pj<ykpi)) {
          break;
      }
      n = n + up;
      pj += 1;
  }
}