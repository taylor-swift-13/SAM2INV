int main1(int a){
  int w4n, hg, eu, k, ufa;
  w4n=55;
  hg=0;
  eu=0;
  k=0;
  ufa=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == hg;
  loop invariant 0 <= hg;
  loop invariant hg <= w4n;
  loop invariant a == \at(a, Pre);
  loop invariant -3 * hg <= eu;
  loop invariant eu <= hg;
  loop invariant -3 * hg * (hg + 1) / 2 <= ufa;
  loop invariant ufa <= hg * (hg + 1) / 2;
  loop assigns hg, eu, k, ufa;
*/
while (hg < w4n) {
      hg = hg + 1;
      eu = eu + ((a + k) % 3 - 1);
      k += 1;
      ufa += eu;
  }
}