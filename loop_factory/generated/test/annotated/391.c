int main1(){
  int g, hg, c1, sy1, t;
  g=45;
  hg=0;
  c1=0;
  sy1=0;
  t=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == hg;
  loop invariant t == 7*c1 + sy1;
  loop invariant c1 >= 0;
  loop invariant g == 45;
  loop invariant 0 <= sy1 < 7;
  loop invariant hg <= g;
  loop assigns t, sy1, c1, hg;
*/
while (hg<=g-1) {
      t += 1;
      sy1 = sy1 + 1;
      if (sy1>=7) {
          sy1 = sy1 - 7;
          c1++;
      }
      hg = hg + 1;
  }
}