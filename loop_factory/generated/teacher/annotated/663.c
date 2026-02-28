int main1(int a,int q){
  int l, k, g, v, c, n;

  l=55;
  k=0;
  g=a;
  v=6;
  c=3;
  n=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant c == 3 + 2*n;
  loop invariant v == n*n + 2*n + 6;
  loop invariant g == \at(a, Pre) + ((n-1)*n*(2*n-1))/6 + n*(n-1) + 7*n;
  loop invariant n <= l+1;

  loop invariant c - 2*n == 3;
  loop invariant g == a + ((n-1)*n*(2*n-1))/6 + n*(n-1) + 7*n;
  loop invariant g == a + (n * (2 * n * n + 3 * n + 37)) / 6;
  loop invariant l == 55;
  loop invariant g == \at(a, Pre) + (n*(n-1)*(2*n-1))/6 + n*n + 6*n;
  loop assigns g, v, c, n;
*/
while (1) {
      if (n>l) {
          break;
      }
      g = g+v;
      v = v+c;
      c = c+2;
      n = n+1;
      g = g+1;
  }

}
