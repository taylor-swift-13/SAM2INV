int main1(int o,int j){
  int ogn, mpq, dg, hj, b51;

  ogn=(j%19)+18;
  mpq=0;
  dg=0;
  hj=-5;
  b51=j;

  while (dg<=ogn-1) {
      hj = dg+5;
      o += mpq;
      dg += 2;
  }

  while (1) {
      if (!(ogn+1<=b51)) {
          break;
      }
      dg += hj;
      mpq = mpq + dg;
      b51 = (ogn+1)-1;
  }

}
