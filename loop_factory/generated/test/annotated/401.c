int main1(int k){
  int p, b2, z, q, xfz;
  p=40;
  b2=p;
  z=0;
  q=2;
  xfz=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b2 <= p;
  loop invariant b2 - p == xfz;
  loop invariant xfz >= 0;
  loop invariant q == (2 + xfz) % 9;
  loop invariant z == (2 + xfz) / 9;
  loop invariant p == 40;
  loop assigns b2, q, xfz, z;
*/
while (1) {
      if (!(b2<p)) {
          break;
      }
      q += 1;
      xfz += 1;
      if (q>=9) {
          q = q - 9;
          z += 1;
      }
      b2++;
  }
}