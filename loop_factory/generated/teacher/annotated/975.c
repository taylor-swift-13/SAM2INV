int main1(int a,int m){
  int z, d, v;

  z=m;
  d=z;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == m;
  loop invariant m == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant d <= z;
  loop invariant v >= 4;
  loop invariant z == \at(m, Pre);
  loop invariant m == \at(m, Pre) && a == \at(a, Pre);
  loop invariant z == \at(m, Pre) && m == \at(m, Pre) && a == \at(a, Pre);

  loop invariant d <= \at(m, Pre);
  loop invariant \at(m, Pre) >= 0 ==> d >= 0;
  loop invariant v % 4 == 0;
  loop invariant a == \at(a,Pre);
  loop invariant m == \at(m,Pre) && z == m && d <= m && v >= 4;
  loop invariant m == \at(m,Pre);
  loop invariant d <= \at(m,Pre);

  loop invariant v % 4 == 0 && v >= 4;
  loop invariant (m >= 0) ==> (d <= m);
  loop invariant (m <= 0) ==> (d <= 0);
  loop assigns d, v;
*/
while (d>=1) {
      v = v*2;
      v = v*v;
      d = d/2;
  }

}
