int main1(){
  int hd, qh, m, x, yr0, ai;

  hd=1;
  qh=hd;
  m=0;
  x=-4;
  yr0=1;
  ai=0;

  while (1) {
      if (!(x<hd)) {
          break;
      }
      m++;
      x = x + 1;
      yr0 = yr0 + qh;
      yr0 = yr0*2;
  }

  while (hd-m>0) {
      ai = ai + yr0;
      yr0 += hd;
      m = 0;
  }

}
