int main1(int a,int n){
  int k, q, v;

  k=a-6;
  q=0;
  v=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == a - 6;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 0 <= q;
  loop invariant (q <= k) || (k < 0);
  loop invariant v >= 8;
  loop invariant k == \at(a, Pre) - 6;
  loop invariant q >= 0 && v >= 8;
  loop invariant q >= 0;
  loop invariant (k < 0) ==> (q == 0);

  loop invariant q >= 0 && k == a - 6 && a == \at(a, Pre) && n == \at(n, Pre) && v >= 0;
  loop invariant k == \at(a,Pre) - 6;
  loop invariant a == \at(a,Pre);
  loop invariant n == \at(n,Pre);

  loop invariant a == \at(a, Pre) && n == \at(n, Pre) && q >= 0 && v >= 8;
  loop invariant (q + 7 <= n + k) ==> v > 0;
  loop assigns q, v;
*/
while (q+1<=k) {
      if (q+7<=n+k) {
          v = v*v;
      }
      q = q+1;
  }

}
