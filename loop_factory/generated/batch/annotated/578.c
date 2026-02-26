int main1(int p,int q){
  int k, s, n, v;

  k=q+5;
  s=1;
  n=s;
  v=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - 2*n + 4*s == 7;
  loop invariant k == \at(q, Pre) + 5;
  loop invariant n >= 1;
  loop invariant s >= 1;
  loop invariant v >= 5;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant k == q + 5;
  loop invariant v >= n;
  loop invariant v == 2*n - 4*s + 7;
  loop assigns n, s, v;
*/
while (1) {
      if (s>=k) {
          break;
      }
      n = n+2;
      s = s+1;
      n = n*2;
      v = v+n;
  }

}
