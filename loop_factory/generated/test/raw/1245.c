int main1(int m){
  int mi, zsz, vi, msv, xjmc, xlzq, lqs4;

  mi=(m%38)+17;
  zsz=0;
  vi=1;
  msv=1;
  xjmc=0;
  xlzq=mi;
  lqs4=4;

  while (vi<=mi) {
      msv += 2;
      zsz += 1;
      xjmc = xjmc*2;
      m += mi;
      vi += msv;
      lqs4 = lqs4%5;
      xlzq += xjmc;
  }

}
