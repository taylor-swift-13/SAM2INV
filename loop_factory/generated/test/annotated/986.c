int main1(int y,int t){
  int e, ckg, uu, zs, bsr, v, z;
  e=57;
  ckg=e;
  uu=0;
  zs=2;
  bsr=-3;
  v=-1;
  z=y*2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bsr == -3 + 2*uu;
  loop invariant zs == 2 + 4*uu;
  loop invariant v == -1 + 3*uu;
  loop invariant y  == \at(y,Pre) + ckg * uu;
  loop invariant z  == 2 * \at(y,Pre) - uu + (3 * uu * (uu + 1)) / 2;
  loop invariant 0 <= uu;
  loop invariant uu <= e;
  loop assigns bsr, zs, uu, v, y, z;
*/
while (uu<e) {
      zs += 4;
      v = v + 3;
      bsr += 2;
      uu = uu + 1;
      y = y + ckg;
      z += v;
  }
}