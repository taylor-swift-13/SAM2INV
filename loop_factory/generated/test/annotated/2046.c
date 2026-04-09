int main1(int z){
  int nr, b55, f4, ir, xbx2;
  nr=91;
  b55=0;
  f4=0;
  ir=0;
  xbx2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= b55;
  loop invariant b55 <= nr;
  loop invariant f4 == b55 * z;
  loop invariant 2 * ir == z * b55 * (b55 - 1);
  loop invariant 6 * xbx2 == z * (b55 - 1) * b55 * (2 * b55 - 1);
  loop invariant nr == 91;
  loop assigns ir, xbx2, f4, b55;
*/
while (b55 < nr) {
      ir = ir + b55 * z;
      xbx2 = xbx2 + b55 * b55 * z;
      f4 += z;
      b55 = b55 + 1;
  }
}