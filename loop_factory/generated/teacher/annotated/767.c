int main1(int a,int n,int p,int q){
  int t, d, z, e, f, k, v;

  t=a+13;
  d=0;
  z=d;
  e=n;
  f=p;
  k=n;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == d;
  loop invariant e == n - d;
  loop invariant t == a + 13;
  loop invariant z >= 0;
  loop invariant d >= 0;
  loop invariant e == \at(n,Pre) - d;
  loop invariant e + z == n;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant d == z;
  loop invariant e + d == n;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant d + e == n;
  loop assigns z, e, d;
*/
while (1) {
      z = z+1;
      e = e-1;
      d = d+1;
  }

}
