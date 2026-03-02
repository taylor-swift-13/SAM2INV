int main1(int m,int p){
  int f, v, r, z;

  f=m;
  v=2;
  r=m;
  z=f;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r - v == m - 2;
  loop invariant z == 2*m - r;
  loop invariant r >= m;
  loop invariant z <= m;
  loop invariant v >= 2;
  loop invariant z + r == 2*m;
  loop invariant m == \at(m, Pre) && p == \at(p, Pre);
  loop invariant r - v == \at(m, Pre) - 2;
  loop invariant z == 2 * \at(m, Pre) - r;
  loop invariant r >= \at(m, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant z + v == m + 2;
  loop invariant r + z == 2*m;
  loop invariant r + z == 2 * m;
  loop invariant f == m;
  loop invariant v - r == 2 - m;
  loop invariant (r - v == m - 2) && (r + z == 2*m) && (f == m) && (r >= m) && (v >= 2) && (z <= m);
  loop invariant m == \at(m,Pre);
  loop invariant p == \at(p,Pre);
  loop assigns r, z, v;
*/
while (1) {
      r = r+1;
      z = z-1;
      v = v+1;
  }

}
