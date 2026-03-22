int main1(int y){
  int hw, j, lbw, re, oiea, g4, jp;
  hw=y;
  j=hw;
  lbw=0;
  re=1;
  oiea=1;
  g4=hw;
  jp=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == hw;
  loop invariant oiea == 1 + 2*lbw;
  loop invariant re == (lbw + 1) * (lbw + 1);
  loop invariant g4 == y * (lbw * lbw + lbw + 2) / 2 + 16 * lbw;
  loop invariant jp == 16 + lbw * y;
  loop invariant g4 == \at(y, Pre) + 16 * lbw + ((y * lbw * (lbw + 1)) / 2);
  loop invariant hw == \at(y, Pre);
  loop invariant lbw >= 0;
  loop invariant j == y;
  loop assigns oiea, lbw, g4, re, jp;
*/
while (1) {
      if (!(re<=hw)) {
          break;
      }
      oiea += 2;
      lbw++;
      g4 += j;
      re += oiea;
      g4 += jp;
      jp = jp + y;
  }
}