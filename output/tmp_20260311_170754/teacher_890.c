int main1(int b,int k){
  int m, l, v, d;

  m=56;
  l=0;
  v=0;
  d=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 56;
  loop invariant d >= 0;
  loop invariant d % 5 == 0;
  loop invariant v >= 0;
  loop invariant v % 5 == 0;
  loop invariant v >= d;
  loop invariant b == \at(b,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant d >= 0 && v >= 0;
  loop invariant d <= v;
  loop invariant v == 0 || v % 3 == 2;
  loop invariant (v == 0) || (v % 3 == 2);

  loop invariant v % 5 == 0 && v >= d && d >= 0 && v <= 3*m + 2;


  loop invariant d <= 5*v;
  loop invariant b == \at(b, Pre) && k == \at(k, Pre);
  loop assigns d, v;
*/
while (v<m) {
      d = d+5;
      v = v+1;
      v = v*3+2;
  }
/*@
  assert !(v<m) &&
         (m == 56);
*/


}
