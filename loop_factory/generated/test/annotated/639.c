int main1(){
  int xf, a, z, luh, qsoq, x;
  xf=1;
  a=0;
  z=0;
  luh=0;
  qsoq=0;
  x=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 4 + (a + 1) / 2;
  loop invariant 0 <= luh;
  loop invariant luh <= 4;
  loop invariant 0 <= qsoq;
  loop invariant qsoq <= 4;
  loop invariant z == 0;
  loop invariant 0 <= a <= xf;
  loop invariant x - a == 4;
  loop invariant (a > 0) ==> luh == (a - 1) % 5;
  loop assigns a, luh, z, qsoq, x;
*/
while (a<xf) {
      luh = a%5;
      if (!(!(a>=x))) {
          qsoq = (a-x)%5;
          z = z+luh-qsoq;
      }
      else {
          z = z + luh;
      }
      a++;
      x = x+(a%2);
  }
}