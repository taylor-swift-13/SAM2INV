int main1(int r){
  int gi, csl, m, tvs, b, tv1, t, e9;

  gi=r+21;
  csl=0;
  m=(r%20)+10;
  tvs=(r%15)+8;
  b=6;
  tv1=gi;
  t=8;
  e9=1;

  while (1) {
      if (!(m>0&&tvs>0)) {
          break;
      }
      if (csl%2==0) {
          m -= 1;
      }
      else {
          tvs -= 1;
      }
      csl++;
      if (b+7<gi) {
          b += csl;
      }
      r = r + m;
      t = t + tvs;
      b += 1;
      tv1 -= 1;
      if (csl+6<=e9+gi) {
          b += t;
      }
  }

}
