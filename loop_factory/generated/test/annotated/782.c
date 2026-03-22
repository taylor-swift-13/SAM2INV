int main1(){
  int h4, zp, xxz, a1, pz;
  h4=34;
  zp=1;
  xxz=h4;
  a1=0;
  pz=zp;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h4 == 34;
  loop invariant 1 <= zp;
  loop invariant zp <= h4;
  loop invariant pz == 1;
  loop invariant a1 >= 0;
  loop invariant xxz > 0;
  loop invariant a1 == 2*xxz - 2*h4;
  loop assigns a1, pz, xxz, zp;
*/
while (zp<h4) {
      xxz = xxz*2;
      a1 += xxz;
      pz = pz%8;
      zp = zp + 1;
  }
}