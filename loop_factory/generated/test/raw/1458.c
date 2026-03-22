int main1(){
  int ksmx, xh, is, e;

  ksmx=(1%33)+16;
  xh=0;
  is=xh;
  e=-4;

  while (1) {
      if (!(xh < ksmx)) {
          break;
      }
      is = is + e;
      xh = xh + ((ksmx - xh) + 1) / 2;
      e += 1;
  }

}
