int main1(){
  int s9, jd, pj, abu, ts3, y6, el, q;

  s9=29;
  jd=0;
  pj=19;
  abu=15;
  ts3=0;
  y6=jd;
  el=0;
  q=3;

  while (1) {
      if (!(jd<=s9-1)) {
          break;
      }
      if (!(ts3!=0)) {
          pj = pj - 1;
          abu = abu + 1;
          ts3 = 0;
      }
      else {
          pj += 1;
          abu--;
          ts3 = 1;
      }
      jd += 1;
      if (jd+5<=pj+s9) {
          q = q%8;
      }
      y6 = y6*3;
      el += abu;
      el = el/3;
  }

}
