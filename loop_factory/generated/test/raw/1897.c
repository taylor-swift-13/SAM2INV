int main1(int t){
  int el3f, n, ikb, an6x, it, e, g0, v6, rp1;

  el3f=47;
  n=0;
  ikb=n;
  an6x=5;
  it=n;
  e=t;
  g0=t;
  v6=0;
  rp1=0;

  while (1) {
      if (!(n < el3f)) {
          break;
      }
      n += 1;
      rp1 += 1;
      if (rp1 >= t) {
          rp1 = 0;
      }
      it += 1;
      ikb++;
      g0++;
      e += 1;
      an6x += ikb;
      if (n+4<=t+el3f) {
          t += 1;
      }
      v6 = v6 + an6x;
      v6 += 4;
  }

}
