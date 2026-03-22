int main1(int y){
  int xk, ij8, z;
  xk=(y%20)+5;
  ij8=(y%20)+5;
  z=(y%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xk == ij8;
  loop invariant ij8 == z;
  loop invariant y == \at(y, Pre);
  loop invariant xk <= ((\at(y, Pre) % 20) + 5);
  loop assigns xk, ij8, z;
*/
while (xk>=1) {
      if (ij8>0) {
          if (z>0) {
              xk = xk - 1;
              ij8--;
              z = z - 1;
          }
      }
  }
}