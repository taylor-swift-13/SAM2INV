int main1(int m,int n){
  int l, u, d;

  l=40;
  u=0;
  d=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 40;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant u >= 0;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant d == \at(n, Pre) || d >= 0;
  loop invariant l == 40 && u >= 0 && m == \at(m, Pre);
  loop invariant d >= \at(n, Pre);
  loop invariant d*(d+1) >= d;
  loop invariant l == 40 && u >= 0;
  loop invariant l == 40 && m == \at(m,Pre) && n == \at(n,Pre);
  loop assigns d, u;
*/
while (1) {
      if (d+6<l) {
          d = d*d+d;
      }
      u = u+1;
  }

}
