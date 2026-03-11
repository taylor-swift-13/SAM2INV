int main1(int g){
  int f, w, zv, p1;

  f=g;
  w=f;
  zv=0;
  p1=1;

  while (w<=f-1) {
      if (!(zv<4)) {
          p1 = -1;
      }
      if (zv<=0) {
          p1 = 1;
      }
      w += 1;
      zv = zv + p1;
  }

}
