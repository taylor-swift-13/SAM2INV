int main1(int a,int n){
  int m, z, j, v;

  m=18;
  z=m;
  j=m;
  v=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant z >= 0;
  loop invariant z <= 18;
  loop invariant j <= 18;
  loop invariant (j - z) % 3 == 0;
  loop invariant 2*j == (5*z - 54);
  loop invariant 0 <= z;
  loop invariant z <= m;
  loop invariant 2*j - 5*z == -54;
  loop invariant v == -3;
  loop invariant m == 18;

  loop invariant 2*j == 5*z - 54;
  loop assigns j, z;
*/
while (z>=2) {
      j = j+v+v;
      j = j+1;
      z = z-2;
  }

}
