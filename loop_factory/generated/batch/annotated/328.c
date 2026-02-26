int main1(int m,int q){
  int g, j, t;

  g=62;
  j=0;
  t=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 0;
  loop invariant t >= m;
  loop invariant (t - m) % 2 == 0;
  loop invariant g == 62;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant ((t - m) % 2) == 0;
  loop invariant 0 <= j;
  loop invariant j <= g;
  loop assigns t;
*/
while (j<=g-1) {
      t = t+2;
      t = t+j;
  }

}
