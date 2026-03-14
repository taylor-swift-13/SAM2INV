int main1(){
  int li, ul8, lb, n, te, ds9n;

  li=1;
  ul8=li;
  lb=ul8;
  n=0;
  te=0;
  ds9n=li;

  while (1) {
      if (!(ul8>=1)) {
          break;
      }
      te = te + li;
      n += lb;
      lb = lb + te;
      ul8 = 0;
  }

  while (ds9n*2<=n) {
      ul8 = ul8 + li;
      lb += n;
      li = li + 3;
      n = (ds9n*2)-1;
  }

}
