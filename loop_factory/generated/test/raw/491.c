int main1(int o,int k){
  int q7, cj, t0, u, o0k, hk;

  q7=k*3;
  cj=1;
  t0=0;
  u=(o%28)+10;
  o0k=0;
  hk=0;

  while (u>t0) {
      u -= t0;
      o0k += q7;
      t0 += 1;
      o0k = o0k + hk;
      hk = hk + o;
  }

  while (q7>cj) {
      q7 = q7 - cj;
      cj++;
      k = k+(q7%7);
      o = o+(cj%8);
      o = o*o+o;
  }

}
