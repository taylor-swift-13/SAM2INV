int main1(int a,int n,int p,int q){
  int b, v, d, g, u, z, x;

  b=17;
  v=3;
  d=q;
  g=a;
  u=n;
  z=5;
  x=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d >= q;
  loop invariant g == a || g == u;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant g <= a;

  loop invariant u == \at(n, Pre);
  loop invariant d >= \at(q, Pre);
  loop invariant g <= \at(a, Pre);

  loop assigns d, g;
*/
while (1) {
      if (u<=g) {
          g = u;
      }
      d = d+1;
  }

}
