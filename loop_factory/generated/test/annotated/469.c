int main1(int c,int o){
  int l, zr, xk, z1, r1z;
  l=12;
  zr=0;
  xk=0;
  z1=0;
  r1z=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r1z == 12 + zr * z1;
  loop invariant z1 <= l;
  loop invariant xk == c * z1;
  loop invariant r1z == 12;
  loop invariant l == 12;
  loop assigns r1z, z1, xk;
*/
while (1) {
      if (!(z1<l)) {
          break;
      }
      r1z += zr;
      z1 = z1 + 1;
      xk = xk + c;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z1 >= 0;
  loop invariant xk >= z1 * c;
  loop invariant zr == c * (xk - 12 * c);
  loop assigns xk, zr, l;
*/
while (xk<=z1-1) {
      xk += 1;
      zr = zr + c;
      l += zr;
  }
}