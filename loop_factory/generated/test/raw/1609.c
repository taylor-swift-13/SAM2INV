int main1(int m){
  int g0r, h9, o88z, zh, lo, ag, fww, emr, s, ht3;

  g0r=m*4;
  h9=0;
  o88z=0;
  zh=0;
  lo=0;
  ag=(m%18)+5;
  fww=h9;
  emr=g0r;
  s=0;
  ht3=0;

  while (ag>=1) {
      zh = zh+m*m;
      ag = ag - 1;
      lo = lo+m*m;
      o88z = o88z+m*m;
      if (s+3<g0r) {
          s = s*emr;
      }
      if (s+5<g0r) {
          s = s*s+m;
      }
      fww = fww + lo;
      ht3 = ht3+(lo%9);
      ht3 = ht3*ht3+fww;
      emr = emr*ht3;
      fww = fww%9;
  }

}
