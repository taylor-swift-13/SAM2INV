int main1(){
  int d, atb, n, pnb, v;

  d=(1%6)+18;
  atb=0;
  n=0;
  pnb=0;
  v=0;

  while (atb < d) {
      v = (n = (pnb = (atb = atb + 1)));
      pnb += pnb;
      atb = d;
  }

}
