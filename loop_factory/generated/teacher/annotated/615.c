int main1(int m,int n){
  int q, k, v, e, p, j;

  q=(n%9)+11;
  k=q;
  v=n;
  e=6;
  p=k;
  j=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == n + 9*(k - q);
  loop invariant q == (\at(n, Pre) % 9) + 11;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant k >= q;
  loop invariant e == 6;
  loop invariant q == (n % 9) + 11;
  loop invariant q == (\at(n,Pre) % 9 + 11);
  loop invariant v == n + 9*(k - (\at(n,Pre) % 9 + 11));
  loop invariant k >= (\at(n,Pre) % 9 + 11);
  loop invariant v >= n;
  loop invariant v - 9*k == n - 9*q;
  loop invariant k <= q;
  loop assigns v, k;
*/
while (1) {
      if (k>=q) {
          break;
      }
      v = v+3;
      k = k+1;
      v = v+e;
  }

}
