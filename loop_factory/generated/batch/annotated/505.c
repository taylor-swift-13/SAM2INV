int main1(int m,int n){
  int z, i, d;

  z=(n%8)+8;
  i=z;
  d=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant i == z;
  loop invariant (d == i) || (d == 0);

  loop invariant z == i;
  loop invariant d == i || d == 0;
  loop invariant z == (n % 8) + 8;
  loop invariant d == 0 || d == z;
  loop invariant d <= i;
  loop invariant d >= 0;
  loop invariant i >= 0;
  loop invariant z == (\at(n, Pre) % 8) + 8;
  loop invariant (d == 0) || (d == i);
  loop invariant 0 <= d;
  loop assigns d;
*/
while (i-3>=0) {
      d = d+3;
      d = d-d;
  }

}
