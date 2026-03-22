int main1(int n,int u){
  int l, ps, fc, bfx, vd, y8d;

  l=17;
  ps=0;
  fc=1;
  bfx=6;
  vd=0;
  y8d=n;

  while (vd<=l) {
      vd += 1;
      ps = ps + fc;
      fc += bfx;
      y8d = y8d + fc;
      bfx += 2;
      y8d = y8d*2;
  }

}
