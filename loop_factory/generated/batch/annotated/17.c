int main1(int k,int q){
  int d, b, v, p;

  d=k;
  b=d;
  v=b;
  p=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant b <= \at(k, Pre);
  loop invariant v == \at(k, Pre) + 2 * \at(k, Pre) * (\at(k, Pre) - b);
  loop invariant d == k;

  loop invariant v == k + 2*p*(k - b);
  loop invariant p == k;
  loop invariant b <= k;
  loop invariant v == d + 2 * p * (d - b);
  loop invariant p == d;
  loop invariant d == \at(k, Pre);
  loop invariant b <= d;
  loop invariant v + 2 * p * b == \at(k,Pre) + 2 * p * \at(k,Pre);
  loop invariant \at(k,Pre) >= 0 ==> (0 <= b && b <= \at(k,Pre));
  loop invariant p == \at(k,Pre);
  loop assigns v, b;
*/
while (b>0) {
      v = v+p+p;
      b = b-1;
  }

}
