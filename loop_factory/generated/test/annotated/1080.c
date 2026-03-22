int main1(){
  int xbp, oiba, c9, vyp, ize;
  xbp=1*4;
  oiba=0;
  c9=(1%28)+10;
  vyp=5;
  ize=xbp;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vyp >= 5;
  loop invariant c9 + oiba*(oiba - 1)/2 == 11;
  loop invariant xbp == 4;
  loop invariant 0 <= oiba;
  loop assigns c9, vyp, oiba;
*/
while (c9>oiba) {
      c9 = c9 - oiba;
      vyp += xbp;
      oiba = oiba + 1;
      vyp = vyp*2+4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oiba >= 0;
  loop invariant ize >= 0;
  loop invariant xbp == 4;
  loop invariant ize <= 4;
  loop invariant vyp >= 5;
  loop assigns vyp, ize, c9, oiba;
*/
while (1) {
      if (!(ize>0)) {
          break;
      }
      vyp = vyp+1*1;
      ize -= 1;
      c9 = c9+1*1;
      oiba = oiba+1*1;
      oiba = oiba*oiba+oiba;
  }
}