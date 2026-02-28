int main1(int a,int b,int m,int n){
  int t, p, i, v, y, u, z, k;

  t=(m%8)+14;
  p=1;
  i=0;
  v=1;
  y=6;
  u=0;
  z=t;
  k=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == 6 + 4 * u;
  loop invariant v == 1 + 2 * u * u + 4 * u;
  loop invariant i == u + (((u - 1) * u * (2 * u - 1)) / 3) + 2 * u * (u - 1);
  loop invariant 0 <= u;
  loop invariant u <= t + 1;
  loop invariant t == (m % 8) + 14;
  loop invariant i == (2*u*u*u + 3*u*u - 2*u) / 3;
  loop invariant 3*i == 2*u*u*u + 3*u*u - 2*u;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant i >= 0;
  loop invariant v >= 1;
  loop invariant y >= 6;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop assigns u, i, v, y;
*/
while (u<=t) {
      u = u+1;
      i = i+v;
      v = v+y;
      y = y+4;
  }

}
