int main1(int x,int q){
  int zk, vnt, aic, g, yn, ksy, oms, x5, tm;

  zk=q+15;
  vnt=0;
  aic=0;
  g=x;
  yn=8;
  ksy=x;
  oms=-1;
  x5=q;
  tm=q+5;

  while (aic<zk) {
      aic += 2;
      if (ksy<=yn) {
          yn = ksy;
      }
      if ((vnt%3)==0) {
          x = x + 1;
      }
      g = g + aic;
      tm = tm + yn;
      ksy = ksy + yn;
      g++;
      ksy -= 1;
      oms = oms + tm;
      x5 = x5 + aic;
  }

}
