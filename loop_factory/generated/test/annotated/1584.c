int main1(int g,int r){
  int xca9, i, wj, oxi, kh, pw1t, x, bh;
  xca9=49;
  i=2;
  wj=0;
  oxi=xca9;
  kh=i;
  pw1t=-2;
  x=g;
  bh=g;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oxi == xca9 - wj;
  loop invariant i == 2;
  loop invariant g == \at(g, Pre) + wj * (xca9 - i);
  loop invariant r == \at(r, Pre) + 3 * wj;
  loop invariant pw1t == -2 + 3 * wj;
  loop invariant kh == 2 + 5 * wj;
  loop invariant bh == \at(g,Pre) + wj;
  loop invariant xca9 == 49;
  loop invariant (\at(g, Pre) + 4 * wj) <= x;
  loop invariant x <= (\at(g, Pre) + 5 * wj);
  loop invariant 0 <= wj <= xca9;
  loop assigns wj, oxi, pw1t, x, r, bh, kh, g;
*/
while (1) {
      if (!(wj<xca9&&oxi>0)) {
          break;
      }
      wj = wj + 1;
      oxi--;
      if (i+3<=i+xca9) {
          pw1t = pw1t + i;
      }
      if (x+7<xca9) {
          x = x + 1;
      }
      r = r + 3;
      pw1t = pw1t + 1;
      bh++;
      kh += 4;
      g = g+xca9-i;
      x += 4;
      kh++;
  }
}