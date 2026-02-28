int main1(int p){
  int m, t, q;

  m=19;
  t=m;
  q=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t % 3 == 1;
  loop invariant p == \at(p, Pre);
  loop invariant m == 19;
  loop invariant t <= m;
  loop invariant t <= 19;
  loop invariant t >= 1;
  loop assigns t;
*/
while (t>2) {
      t = t-3;
  }

}
