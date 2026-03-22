int main1(int w){
  int tn7, ec, niv, j3, z, ma, yi;
  tn7=51;
  ec=0;
  niv=0;
  j3=1;
  z=6;
  ma=0;
  yi=ec;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j3 == 2*ma*ma + 4*ma + 1;
  loop invariant z == 6 + 4*ma;
  loop invariant niv == ((ma-1)*ma*(2*ma-1))/3 + 2*ma*(ma-1) + ma;
  loop invariant yi == (((ma-1)*ma*(2*ma-1))/3) + 6*ma*(ma-1) + 17*ma;
  loop invariant 0 <= ma <= tn7 + 1;
  loop assigns niv, ma, j3, z, w, yi;
*/
while (1) {
      if (!(ma<=tn7)) {
          break;
      }
      niv = niv + j3;
      ma += 1;
      j3 += z;
      z += 4;
      w += ma;
      yi = yi+j3+z;
  }
}