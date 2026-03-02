int main1(int a,int b){
  int m, u, z, v;

  m=71;
  u=1;
  z=0;
  v=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 0;
  loop invariant z >= 0;
  loop invariant z - 2*v >= 0;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant v <= z;
  loop invariant v >= 0 && z >= 0 && v <= z;

  loop invariant z >= 2 * v;
  loop invariant z <= 3*v + 1 && a == \at(a, Pre) && b == \at(b, Pre);

  loop invariant m == 71 && a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant z + 1 - 2 * v >= 1;
  loop invariant m == 71;
  loop invariant 0 <= z && 0 <= v;

  loop assigns v, z;
*/
while (z<m) {
      v = v+z;
      z = z+1;
      z = z+v+v;
  }

}
