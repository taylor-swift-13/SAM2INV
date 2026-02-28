int main1(int a,int n){
  int m, z, j, v;

  m=18;
  z=m;
  j=m;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == v*v + 9;
  loop invariant z + 2*v == 12;
  loop invariant z >= 0;
  loop invariant m == 18;
  loop invariant 2*v + z == m - 6;
  loop invariant z <= m;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant z == 12 - 2*v;
  loop invariant z <= 18;
  loop invariant v >= -3;
  loop assigns j, v, z;
*/
while (z>=2) {
      j = j+v+v;
      j = j+1;
      v = v+1;
      z = z-2;
  }

}
