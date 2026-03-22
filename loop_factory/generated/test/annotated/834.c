int main1(){
  int r3, lo, p, mfi, m, hv;
  r3=77;
  lo=0;
  p=lo;
  mfi=lo;
  m=0;
  hv=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mfi == 0;
  loop invariant hv == 3;
  loop invariant p >= 0;
  loop invariant 0 <= m <= r3;
  loop invariant (p % 2) == (m % 2);
  loop invariant (m == 0) ==> (p == 0);
  loop assigns m, p, mfi, hv;
*/
while (1) {
      if (m>=r3) {
          break;
      }
      m++;
      p = p*hv+1;
      mfi = mfi*hv;
      hv = hv+(mfi%9);
  }
}