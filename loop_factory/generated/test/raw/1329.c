int main1(int k){
  int le, hqy, dyf, ex, u, re;

  le=(k%11)+20;
  hqy=le+6;
  dyf=0;
  ex=1;
  u=1;
  re=hqy;

  while (1) {
      if (!(ex<=le)) {
          break;
      }
      u += 2;
      dyf += 1;
      re = re + le;
      ex = ex + u;
  }

}
