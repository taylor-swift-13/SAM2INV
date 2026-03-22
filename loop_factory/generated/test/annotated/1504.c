int main1(){
  int zg99, v3, yxp, b0g, qs, w9iq, yg, brs, y9;
  zg99=72;
  v3=0;
  yxp=4;
  b0g=0;
  qs=-2;
  w9iq=10;
  yg=0;
  brs=v3;
  y9=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yxp - b0g == 4;
  loop invariant v3 == 0 || v3 == zg99;
  loop invariant qs == -2;
  loop invariant (yg >= 0);
  loop invariant w9iq == 10 + 5 * yg;
  loop invariant 0 <= zg99 - v3;
  loop assigns yxp, b0g, qs, y9, yg, brs, w9iq, v3;
*/
while (1) {
      if (!(v3<=zg99-1)) {
          break;
      }
      if (qs==zg99+1) {
          yxp = yxp + 3;
          b0g = b0g + 3;
      }
      else {
          yxp += 2;
          b0g += 2;
      }
      if (qs==zg99) {
          yxp += 1;
          qs = qs + 1;
      }
      y9 = y9 + b0g;
      yg += 1;
      brs += qs;
      w9iq = w9iq + 5;
      v3 = zg99;
  }
}