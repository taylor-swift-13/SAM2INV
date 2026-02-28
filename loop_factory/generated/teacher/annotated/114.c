int main1(int q){
  int n, k, p, v;

  n=24;
  k=0;
  p=k;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 3*p;
  loop invariant k <= n;
  loop invariant p >= 0;
  loop invariant n == 24;
  loop invariant q == \at(q, Pre);
  loop invariant 3*p == k;
  loop invariant p <= n/3;
  loop invariant k >= 0;
  loop assigns p, k;
*/
while (k<=n-3) {
      p = p+1;
      k = k+3;
  }

}
