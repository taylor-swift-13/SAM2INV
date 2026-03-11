int main1(int b,int k){
  int n, t, v, q;

  n=32;
  t=0;
  v=4;
  q=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant 0 <= t;
  loop invariant t <= n;
  loop invariant v >= 4*(t+1);
  loop invariant 0 <= t && t <= n;
  loop invariant v % 4 == 0;
  loop invariant v >= 4;
  loop invariant b == \at(b, Pre) && k == \at(k, Pre);
  loop invariant n == 32;
  loop invariant (3*v + 4) % 16 == 0;
  loop invariant 0 <= t && t <= n && b == \at(b, Pre) && k == \at(k, Pre);
  loop invariant v % 4 == 0 && v >= 4;
  loop invariant b == \at(b, Pre) && k == \at(k, Pre) && v >= 4;
  loop assigns t, v;
*/
while (t<=n-1) {
      v = v*4+4;
      t = t+1;
  }
/*@
  assert !(t<=n-1) &&
         (b == \at(b, Pre));
*/


}
