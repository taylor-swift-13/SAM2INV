int main1(){
  int ksmx, xh, is, e;
  ksmx=(1%33)+16;
  xh=0;
  is=xh;
  e=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= xh;
  loop invariant xh <= ksmx;
  loop invariant 2*is == e*e - e - 20;
  loop assigns is, xh, e;
*/
while (1) {
      if (!(xh < ksmx)) {
          break;
      }
      is = is + e;
      xh = xh + ((ksmx - xh) + 1) / 2;
      e += 1;
  }
}