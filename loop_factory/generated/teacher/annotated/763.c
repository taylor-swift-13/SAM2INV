int main1(int a,int n,int p,int q){
  int e, z, d, v, j;

  e=a;
  z=3;
  d=-4;
  v=5;
  j=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant d == 2*z - 10;
  loop invariant v == z*z - 9*z + 23;
  loop invariant 3*j == z*z*z - 12*z*z + 56*z - 78;
  loop invariant e == a;
  loop invariant z >= 3;
  loop invariant j == 3 + ((z - 3) * (z - 2) * (2*z - 5)) / 6 - 3 * ((z - 3) * (z - 2)) / 2 + 5 * (z - 3);
  loop invariant 4*v == d*d + 2*d + 12;
  loop invariant d >= -4;
  loop assigns d, v, j, z;
*/
while (1) {
      d = d+2;
      v = v+d;
      j = j+v;
      z = z+1;
  }

}
