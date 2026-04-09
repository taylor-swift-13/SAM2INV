int main1(){
  int hm, a36, bn, n, f26;

  hm=1+21;
  a36=0;
  bn=0;
  n=25;
  f26=0;

  while (1) {
      if (!(a36 < hm*hm)) {
          break;
      }
      f26 = f26 + (a36++, (bn = 1 - bn), bn);
      bn = bn+f26-f26;
      n = n+f26-f26;
      a36 = hm*hm;
  }

}
