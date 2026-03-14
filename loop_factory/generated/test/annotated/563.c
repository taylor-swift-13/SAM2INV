int main1(int r){
  int xt, f7, z, is, t;
  xt=r*2;
  f7=xt;
  z=1;
  is=0;
  t=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant is == ((z - 1) * z * (2 * z - 1)) / 6;
  loop invariant t == 3 * z - 7;
  loop invariant r == \at(r, Pre) + (z - 1) * f7;
  loop invariant xt == 2 * \at(r,Pre);
  loop assigns is, t, r, z;
*/
while (z<=xt) {
      is = is+z*z;
      t = t + 3;
      r = r + f7;
      z += 1;
  }
}