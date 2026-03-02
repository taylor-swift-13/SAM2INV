int main1(int m,int n){
  int d, j, z, k;

  d=n+17;
  j=0;
  z=2;
  k=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == \at(n, Pre) + 17 && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant (z == 0 || z == 2 || z == 6) && j >= 0;
  loop invariant 0 <= z && z <= 6;
  loop invariant j >= 0;
  loop invariant d == \at(n, Pre) + 17;
  loop invariant n == \at(n, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= z && z <= 6 && j >= 0 && d == \at(n, Pre) + 17;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre) && 0 <= z && z <= 6 && j >= 0;
  loop invariant 0 <= z && z <= 6 && j >= 0;
  loop invariant d == \at(n, Pre) + 17 && n == \at(n, Pre) && m == \at(m, Pre);
  loop assigns z, j;
*/
while (1) {
      z = z*z+z;
      z = z%7;
      j = j+1;
  }

}
