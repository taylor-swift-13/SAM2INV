int main1(int k,int n){
  int g, d, v;

  g=n;
  d=0;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == n && k == \at(k, Pre) && n == \at(n, Pre);
  loop invariant d >= 0;
  loop invariant d >= 0 && g == \at(n, Pre);
  loop invariant n == \at(n, Pre) && k == \at(k, Pre);
  loop invariant g == \at(n,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant g == \at(n, Pre);
  loop invariant g == \at(n,Pre) && n == \at(n,Pre) && k == \at(k,Pre) && d >= 0;
  loop invariant (n == 0) ==> (v == 0);
  loop invariant v >= n;
  loop invariant g == n;
  loop invariant n == \at(n, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant v >= g;
  loop invariant g == \at(n,Pre) && k == \at(k,Pre) && n == \at(n,Pre);
  loop invariant g == n && d >= 0;
  loop invariant n == \at(n, Pre) && k == \at(k, Pre) && g == n;
  loop assigns d, v;
*/
while (1) {
      v = v*2;
      v = v*v+v;
      d = d+1;
  }

}
