int main1(int j){
  int s5k, kh, ebol, pj, k;
  s5k=19;
  kh=0;
  ebol=-2;
  pj=s5k;
  k=kh;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ebol <= s5k);
  loop invariant k == (ebol + 2) * s5k - ((ebol - 3) * (ebol + 2)) / 2;
  loop invariant k == ((ebol + 2) * (2*s5k + 3 - ebol)) / 2;
  loop invariant 2*k == -ebol*ebol + 39*ebol + 82;
  loop invariant -2 <= ebol <= 19;
  loop invariant k == (s5k + 2) * (ebol + 2) - ((ebol + 2) * (ebol + 1)) / 2;
  loop assigns k, ebol, pj;
*/
while (1) {
      if (!(ebol<s5k)) {
          break;
      }
      pj = s5k-ebol;
      k += pj;
      ebol++;
  }
}