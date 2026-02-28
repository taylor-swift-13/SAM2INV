int main1(int q){
  int n, k, p, v;

  n=24;
  k=0;
  p=k;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p % 49 == 0;
  loop invariant p >= 0;
  loop invariant n == 24;
  loop invariant v == 24;
  loop invariant q == \at(q, Pre);
  loop invariant p <= 49;
  loop invariant p % (1 + 2*v) == 0;
  loop invariant v == n;
  loop assigns p;
*/
while (p<n) {
      if (p<n) {
          p = p+1;
      }
      p = p+v+v;
  }

}
