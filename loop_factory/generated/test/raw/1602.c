int main1(int y){
  int x, sohf, a, r, k9x1, sg9, ot, jaq;

  x=y;
  sohf=x;
  a=3;
  r=3;
  k9x1=0;
  sg9=7;
  ot=0;
  jaq=3;

  while (sohf<x) {
      if (!(!(sohf%3==0))) {
          if (a>0) {
              a -= 1;
              k9x1 = k9x1 + 1;
          }
      }
      else {
          if (a<sg9) {
              a++;
              r = r + 1;
          }
      }
      sohf = sohf + 1;
      ot += 1;
      y = y + a;
      jaq = jaq + ot;
      sg9 = sg9 + ot;
  }

}
