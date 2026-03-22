int main1(){
  int xpp, uqr, duj, p, ni;

  xpp=1;
  uqr=0;
  duj=1;
  p=1;
  ni=xpp;

  while (duj<=xpp) {
      p = p+2*duj-1;
      duj += 1;
      ni += xpp;
  }

  while (1) {
      if (!(duj<xpp)) {
          break;
      }
      p = xpp-duj;
      duj += 8;
      uqr += xpp;
  }

}
