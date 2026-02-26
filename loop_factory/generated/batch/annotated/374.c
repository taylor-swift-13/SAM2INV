int main1(int b,int n){
  int k, i, v, d;

  k=67;
  i=0;
  v=0;
  d=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 67;
  loop invariant 0 <= i;
  loop invariant i <= k;
  loop invariant v >= 0;
  loop invariant (v == 0 ==> d == \at(n, Pre));
  loop invariant (v >= 1 ==> d == k - (v - 1));
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant i == 0;
  loop invariant (v == 0 && d == n) || (v >= 1 && d + v == k + 1);
  loop invariant (v == 0 ==> d == n);
  loop invariant (v > 0 ==> d + v == k + 1);
  loop invariant i <= k - 1;
  loop assigns d, v;
*/
while (i<=k-1) {
      d = k-v;
      v = v+1;
  }

}
