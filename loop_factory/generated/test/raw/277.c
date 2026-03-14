int main1(int z){
  int yzam, a, nu, ltp, ls, bif;

  yzam=63;
  a=2;
  nu=29;
  ltp=0;
  ls=1;
  bif=0;

  while (1) {
      if (!(nu>0&&a<yzam)) {
          break;
      }
      if (nu<=ls) {
          bif = nu;
      }
      else {
          bif = ls;
      }
      a++;
      ltp = ltp + bif;
      nu = nu - bif;
      ls++;
  }

}
