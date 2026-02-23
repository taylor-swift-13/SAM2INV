int main1(int b,int n){
  int q, k, m, g, v;

  q=35;
  k=q;
  m=k;
  g=n;
  v=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m + 5 * k == 210;
  loop invariant 0 <= k && k <= 35;
  loop invariant 35 <= m && m <= 210;
  loop invariant k >= 0;
  loop invariant k <= q;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant k <= 35;
  loop invariant q == 35;
  loop invariant m >= 35 && m <= 210;
  loop invariant m == 210 - 5*k;
  loop assigns m, k;
*/
while (k>0) {
      m = m+5;
      k = k-1;
  }

}
