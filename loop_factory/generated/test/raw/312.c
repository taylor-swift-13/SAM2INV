int main1(){
  int t1i, cp, dfq, k, fa;

  t1i=1+25;
  cp=0;
  dfq=4;
  k=0;
  fa=1;

  while (1) {
      if (!(k<t1i)) {
          break;
      }
      k += 1;
      dfq = dfq + 1;
  }

  while (1) {
      if (!(fa<dfq)) {
          break;
      }
      cp++;
      fa++;
  }

}
