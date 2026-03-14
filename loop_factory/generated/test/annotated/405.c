int main1(){
  int wj, pf, l, tsd5;
  wj=1;
  pf=0;
  l=1;
  tsd5=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == pf + 1;
  loop invariant 0 <= pf;
  loop invariant pf <= wj;
  loop invariant wj == 1;
  loop invariant 1 <= l;
  loop invariant l <= 7;
  loop invariant (tsd5 == 1) || (tsd5 == -1);
  loop assigns l, pf, tsd5;
*/
while (pf<wj) {
      if (!(l<7)) {
          tsd5 = -1;
      }
      if (l<=1) {
          tsd5 = 1;
      }
      l += tsd5;
      pf++;
  }
}