int main1(int o){
  int f, p, k, m, mw, fw;

  f=o;
  p=1;
  k=0;
  m=1;
  mw=1;
  fw=p;

  while (m<=f) {
      k += 1;
      mw += 2;
      m += mw;
      fw += mw;
  }

}
