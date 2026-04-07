int main1(int b){
  int oq, r6, ocv, sx, x2, wcl, eb, xs, bw, uk;

  oq=b-1;
  r6=0;
  ocv=b;
  sx=2;
  x2=0;
  wcl=0;
  eb=b*2;
  xs=r6;
  bw=1;
  uk=0;

  while (1) {
      if (!(r6 < oq)) {
          break;
      }
      r6 = r6 + 1;
      if (((r6 % 2) == 0)) {
          ocv++;
      }
      else {
          sx++;
      }
      if (xs+2<oq) {
          xs += uk;
      }
      wcl += ocv;
      b = b + sx;
      uk += 2;
      x2 = x2 + sx;
      x2 += 4;
      eb += 2;
      eb = b-eb;
      bw = bw + eb;
  }

}
