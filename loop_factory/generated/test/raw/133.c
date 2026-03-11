int main1(int g){
  int d6, trp, czm, n;

  d6=g;
  trp=d6;
  czm=2;
  n=6;

  while (1) {
      if (!(trp<d6)) {
          break;
      }
      czm += 4;
      trp = trp + 1;
      n += 4;
  }

}
