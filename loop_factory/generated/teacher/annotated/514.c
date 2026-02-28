int main1(int k,int q){
  int n, d, v, x;

  n=q+18;
  d=0;
  v=n;
  x=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == n + 2*d;
  loop invariant x == n*(d+1) + d*d;
  loop invariant d <= n || n < 0;
  loop invariant q == \at(q, Pre);
  loop invariant k == \at(k, Pre);

  loop invariant 0 <= d;
  loop invariant x == n*(1 + d) + d*d;

  loop invariant x == n + d*n + d*d;
  loop invariant d >= 0;
  loop invariant v >= n;
  loop invariant v - 2*d == n;
  loop assigns v, d, x;
*/
while (1) {
      if (d>=n) {
          break;
      }
      v = v+1;
      d = d+1;
      v = v+1;
      x = x-1;
      x = x+v;
  }

}
