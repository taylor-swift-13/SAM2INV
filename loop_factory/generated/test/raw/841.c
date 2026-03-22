int main1(){
  int a, y, omd0, sn, sin, h, vw;

  a=1;
  y=0;
  omd0=a;
  sn=12;
  sin=a;
  h=(1%6)+2;
  vw=y;

  while (1) {
      if (sin>=a) {
          break;
      }
      omd0 = omd0*h+1;
      sn = sn*h;
      sin = sin + 1;
      vw = vw + sn;
  }

}
