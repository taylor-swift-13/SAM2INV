int main1(){
  int t05h, lnen, jmh, ozw, u, d;

  t05h=(1%18)+15;
  lnen=0;
  jmh=0;
  ozw=-2;
  u=-2;
  d=0;

  while (ozw<t05h) {
      ozw++;
      jmh++;
      u += 2;
      d = d + lnen;
  }

  while (1) {
      u = u+t05h*d;
      t05h = t05h + u;
      t05h = t05h*3+1;
      d++;
      if (d>=jmh) {
          break;
      }
  }

}
