int main1(int m){
  int y, f0t, ky, p, pvf, lwy, cc;

  y=20;
  f0t=2;
  ky=0;
  p=0;
  pvf=0;
  lwy=(m%18)+5;
  cc=y;

  while (lwy>0) {
      pvf = pvf+m*m;
      cc += f0t;
      ky = ky+m*m;
      p = p+m*m;
      lwy--;
  }

  while (1) {
      if (!(ky>lwy)) {
          break;
      }
      ky -= lwy;
      lwy = lwy + 1;
      y = y+(lwy%2);
      m += ky;
      cc = cc+(ky%3);
  }

}
