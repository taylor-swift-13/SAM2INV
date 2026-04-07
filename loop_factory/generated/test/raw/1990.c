int main1(int o){
  int t, pf, kx, v57;

  t=o;
  pf=0;
  kx=0;
  v57=5;

  while (pf < t) {
      v57 = v57 + (pf < t/2 ? 1 : -1);
      kx += t;
      pf++;
      kx += 1;
  }

}
