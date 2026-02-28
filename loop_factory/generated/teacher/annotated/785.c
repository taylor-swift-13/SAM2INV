int main1(int p,int q){
  int t, m, n, v;

  t=68;
  m=1;
  n=m;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == 4*m - 3;
  loop invariant m <= t;
  loop invariant t == 68;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant m >= 1;
  loop invariant 1 <= m;
  loop invariant n <= 4*t - 3;
  loop assigns m, n;
*/
while (1) {
      if (m>=t) {
          break;
      }
      n = n+3;
      m = m+1;
      n = n+1;
  }

}
