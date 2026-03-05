int main85(int u,int m){
  int l, ig, kbp, rg, t, g, s;

  l=47;
  ig=0;
  kbp=2;
  rg=5;
  t=u;
  g=u;
  s=8;

  while (ig<l) {
      rg = rg + 3;
      ig++;
      kbp = kbp + 3;
      t += 2;
      s = s + kbp;
      g = (g+kbp)%5;
  }

}
