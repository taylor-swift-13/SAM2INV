int main1(int m){
  int t1m, s0z, cj, g8, sg, t;
  t1m=42;
  s0z=0;
  cj=2;
  g8=0;
  sg=t1m;
  t=m;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g8 == cj*(cj - 2);
  loop invariant m == \at(m, Pre) + 2*(cj - 2);
  loop invariant t == \at(m, Pre) + 42*(cj - 2);
  loop invariant t1m == 42;
  loop invariant s0z == 0;
  loop invariant sg == (t1m - s0z) * (cj - 1);
  loop invariant 2 <= cj <= t1m + 1;
  loop assigns g8, t, m, cj, sg;
*/
while (cj<=t1m) {
      g8 = g8+2*cj-1;
      t = t+t1m-s0z;
      m += 2;
      cj++;
      sg = sg+t1m-s0z;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s0z == 0;
  loop invariant t1m == 42;
  loop invariant (cj % 4) == 3;
  loop invariant 3 <= cj;
  loop assigns cj;
*/
while (cj<=s0z-4) {
      cj += 4;
  }
}