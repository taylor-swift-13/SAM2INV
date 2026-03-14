int main1(){
  int v6, y, lt, fvsz, kip2, w4;

  v6=1;
  y=v6;
  lt=1;
  fvsz=0;
  kip2=y;
  w4=y;

  while (fvsz<v6) {
      kip2 += v6;
      lt += 1;
      fvsz++;
      kip2 = kip2 + w4;
  }

  while (w4<v6) {
      w4 = w4 + 1;
      kip2 += 1;
      fvsz = fvsz + y;
  }

}
