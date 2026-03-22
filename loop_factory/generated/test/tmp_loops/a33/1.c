int main1(){
  int xw, q5m, pf, u, h, c4b, k6;

  xw=1*2;
  q5m=0;
  pf=0;
  u=2;
  h=0;
  c4b=xw;
  k6=xw;

  while (q5m<xw) {
      u = u + 1;
      h += 1;
      if (u>=9) {
          u = u - 9;
          pf++;
      }
      q5m += 1;
      if (c4b+3<xw) {
          c4b = c4b + 1;
      }
      c4b = c4b + 1;
      k6 += h;
      k6 = k6 + c4b;
  }

}
