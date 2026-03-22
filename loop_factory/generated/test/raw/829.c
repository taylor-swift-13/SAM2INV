int main1(int d){
  int f, e3, x3, fq, t87, nne;

  f=d-4;
  e3=0;
  x3=8;
  fq=f;
  t87=(d%6)+2;
  nne=d;

  while (fq<f) {
      e3 = e3*t87+d;
      x3 = x3*t87;
      fq += 1;
      t87 = t87 + fq;
      nne = nne + 1;
  }

}
