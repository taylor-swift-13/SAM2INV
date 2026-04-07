int main1(int w){
  int v, tj, kzo, ztj;

  v=20;
  tj=0;
  kzo=0;
  ztj=0;

  while (1) {
      if (!(tj < v)) {
          break;
      }
      ztj = ztj + (w - ztj) / (tj + 1);
      kzo = ztj;
      tj = tj + 1;
  }

}
