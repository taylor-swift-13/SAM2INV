int main1(){
  int oqcm, m, cu, mj, zr0, ie;
  oqcm=(1%8)+5;
  m=oqcm;
  cu=90;
  mj=0;
  zr0=1;
  ie=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cu + mj == 90;
  loop invariant m - zr0 == 5;
  loop invariant 0 <= cu;
  loop invariant 1 <= zr0;
  loop invariant m - oqcm == zr0 - 1;
  loop invariant 0 <= mj;
  loop invariant m <= oqcm;
  loop invariant 0 <= ie;
  loop invariant ie <= zr0;
  loop assigns cu, mj, m, zr0, ie;
*/
while (cu>0&&m<oqcm) {
      if (cu<=zr0) {
          ie = cu;
      }
      else {
          ie = zr0;
      }
      mj += ie;
      cu -= ie;
      m++;
      zr0 += 1;
  }
}