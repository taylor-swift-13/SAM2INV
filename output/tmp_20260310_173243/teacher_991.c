int main1(int a,int q){
  int b, j, m, z;

  b=23;
  j=b;
  m=4;
  z=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*(m - 4) == z*(23 - j) && z == 23 && b == 23;
  loop invariant j % 4 == 23 % 4 && 3 <= j && j <= 23;
  loop invariant 2*m + z*j == 537;
  loop invariant j % 4 == b % 4;
  loop invariant 0 <= j && j <= b;
  loop invariant z == b;
  loop invariant a == \at(a, Pre) && q == \at(q, Pre);
  loop invariant 2*(m - 4) == z*(23 - j);
  loop invariant j <= 23;
  loop invariant j >= 3;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant m == 4 + ((b - j) / 4) * (2 * z);
  loop invariant 3 <= j && j <= b;
  loop invariant z == 23 && a == \at(a, Pre) && q == \at(q, Pre);
  loop invariant j % 4 == 3;
  loop invariant 3 <= j <= 23;
  loop invariant 2*(m - 4) == (23 - j)*z;
  loop invariant 0 <= j && j <= 23;
  loop invariant m == 4 + 2*z*((b - j)/4);
  loop invariant z == 23;
  loop invariant j >= 0;
  loop assigns j, m;
*/
while (j>=4) {
      m = m+z+z;
      j = j-4;
  }
/*@
  assert !(j>=4) &&
         (2*(m - 4) == z*(23 - j) && z == 23 && b == 23);
*/


}
