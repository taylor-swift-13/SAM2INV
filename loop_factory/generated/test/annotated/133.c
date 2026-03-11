int main1(int g){
  int d6, trp, czm, n;
  d6=g;
  trp=d6;
  czm=2;
  n=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant czm - 2 == 4*(trp - d6);
  loop invariant trp <= d6;
  loop invariant d6 == g;
  loop invariant n - 4*(trp - d6) == 6;
  loop invariant d6 == \at(g, Pre);
  loop invariant trp >= \at(g, Pre);
  loop assigns czm, trp, n;
*/
while (1) {
      if (!(trp<d6)) {
          break;
      }
      czm += 4;
      trp = trp + 1;
      n += 4;
  }
}