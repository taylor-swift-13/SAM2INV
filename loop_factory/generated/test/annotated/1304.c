int main1(int q,int o){
  int bcmr, kdf, oq, n;
  bcmr=1;
  kdf=o;
  oq=o;
  n=(o%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kdf == oq;
  loop invariant n <= ((\at(o,Pre) % 35) + 8);
  loop invariant o == \at(o, Pre);
  loop invariant kdf >= o;
  loop invariant bcmr >= 1;
  loop assigns bcmr, kdf, oq, q, n;
*/
while (1) {
      if (!(n>0)) {
          break;
      }
      bcmr = bcmr+kdf*kdf;
      oq = oq+n*n;
      kdf = kdf+n*n;
      q = q + kdf;
      n = n - 1;
  }
}