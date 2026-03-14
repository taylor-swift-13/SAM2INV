int main1(){
  int tsh, m, v, km, qu1, k, h;

  tsh=(1%36)+15;
  m=1;
  v=0;
  km=(1%28)+10;
  qu1=m;
  k=-5;
  h=-6;

  while (km>v) {
      km -= v;
      v++;
      k += 2;
      qu1 = qu1 + 1;
      h = h+(v%8);
  }

  while (h>=1) {
      k = k+1*1;
      h = h - 1;
      tsh = tsh+1*1;
      qu1 = qu1+1*1;
      tsh += v;
  }

}
