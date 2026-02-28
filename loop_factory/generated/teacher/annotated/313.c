int main1(int m,int p){
  int n, l, x;

  n=22;
  l=0;
  x=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant n == 22;
  loop invariant l >= 0;
  loop invariant l <= n - 2;
  loop invariant x % 2 == 0;
  loop invariant l == 0;
  loop invariant x >= n;
  loop invariant (x - n) % 2 == 0;
  loop invariant (l <= n - 3);
  loop invariant (x >= n);
  loop invariant (x % 2 == 0);
  loop invariant l <= n - 3;
  loop invariant 0 <= l <= n - 3;
  loop assigns x;
*/
while (l<=n-3) {
      x = x+2;
      if (x+4<n) {
          x = x+x;
      }
  }

}
