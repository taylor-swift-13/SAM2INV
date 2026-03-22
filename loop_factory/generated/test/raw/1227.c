int main1(int c){
  int xh, nf, eg, o, lmk;

  xh=48;
  nf=c;
  eg=0;
  o=-2;
  lmk=1;

  while (lmk<=xh) {
      nf += eg;
      eg = eg + o;
      o += 6;
      lmk = lmk + 1;
      c += lmk;
  }

}
