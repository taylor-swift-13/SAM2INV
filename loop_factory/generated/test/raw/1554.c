int main1(int w,int x){
  int trkc, af, kw, hq, vz3, lhzg, m, cx, pu;

  trkc=x*5;
  af=0;
  kw=w;
  hq=8;
  vz3=w;
  lhzg=af;
  m=w;
  cx=trkc;
  pu=4;

  while (1) {
      if (!(af < trkc)) {
          break;
      }
      if (!(!((af % 2) == 0))) {
          kw++;
          af++;
      }
      else {
          hq++;
          cx = cx + 1;
          af++;
      }
      if ((af%7)==0) {
          w = hq+kw;
      }
      pu = pu + cx;
      x = x + hq;
      vz3 = vz3 + 1;
      vz3 += 4;
      lhzg = lhzg + vz3;
      m = m + lhzg;
  }

}
