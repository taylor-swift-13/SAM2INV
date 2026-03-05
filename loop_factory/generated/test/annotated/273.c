int main1(){
  int z1, z, d, kw;
  z1=1;
  z=2;
  d=z;
  kw=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 2;
  loop invariant z1 == 1;
  loop invariant kw >= -2;
  loop invariant d >= 2;
  loop assigns d, kw;
*/
while (z<z1) {
      if (z<z1/2) {
          d += kw;
      }
      else {
          d++;
      }
      kw = kw + z1;
  }
}