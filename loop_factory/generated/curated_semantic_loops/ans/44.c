int main1(int n,int q){
  int m, d, a, b;

  m=(n%28)+10;
  d=m;
  a=m;
  b=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == (\at(n, Pre) % 28) + 10;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant d <= m;
  loop invariant m == \at(n, Pre) % 28 + 10;
  loop invariant n == \at(n, Pre) && q == \at(q, Pre);
  loop invariant (m >= 0 ==> 0 <= d && d <= m) && (m <= 0 ==> m <= d && d <= 0);

  loop assigns d;
*/
while (d>=1) {
      d = d/2;
  }
/*@
  assert !(d>=1) &&
         (m == (\at(n, Pre) % 28) + 10);
*/


}
