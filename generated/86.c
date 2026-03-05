int main86(int p){
  int oq4, oih, pcxs, ti, qu;

  oq4=p+23;
  oih=-3;
  pcxs=p;
  ti=oq4;
  qu=0;

  while (oih<oq4) {
      oih += 4;
      ti = ti+(oih%2);
      qu = qu+(oih%5);
      p = p+(oih%7);
      pcxs = pcxs + ti;
      ti += qu;
  }

  while (1) {
      if (!(oih>=1)) {
          break;
      }
      qu += 4;
      oih -= 4;
      p += oih;
      p = p*p;
  }

}
