int main1(){
  int nf9, pf, c;

  nf9=(1%30)+4;
  pf=0;
  c=nf9;

  while (pf<nf9) {
      c += 2;
      pf++;
      c = c + c;
  }

}
