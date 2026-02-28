int main1(int b,int q){
  int n, t, k, u;

  n=q;
  t=0;
  k=-2;
  u=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n == q;
  loop invariant u == n;
  loop invariant t == 0;
  loop invariant k >= -2;
  loop invariant (t < n/2) ==> ((k + 2) % (u + 5) == 0);
  loop invariant t >= 0;
  loop invariant n == \at(q, Pre);
  loop assigns k;
*/
while (t<=n-3) {
      if (t<n/2) {
          k = k+u;
      }
      else {
          k = k+1;
      }
      k = k+5;
  }

}
