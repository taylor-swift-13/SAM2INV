int main1(){
  int pj, u9i, gr, xp;
  pj=(1%25)+18;
  u9i=0;
  gr=3;
  xp=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xp == pj * u9i;
  loop invariant gr == 3 + u9i*(u9i - 1) / 2;
  loop invariant 0 <= u9i;
  loop invariant u9i <= pj;
  loop assigns gr, xp, u9i;
*/
while (1) {
      if (!(u9i<=pj-1)) {
          break;
      }
      gr = gr + u9i;
      xp += pj;
      u9i = u9i + 1;
  }
}