int main1(int g){
  int kc2, l, ait, v, s, bz, y, x4;

  kc2=75;
  l=1;
  ait=9;
  v=0;
  s=g;
  bz=-4;
  y=l;
  x4=kc2;

  while (1) {
      if (!(l<kc2)) {
          break;
      }
      if (!(!(l%2==0))) {
          if (ait>0) {
              ait--;
              v++;
          }
      }
      else {
          if (v>0) {
              v -= 1;
              ait = ait + 1;
          }
      }
      x4 += ait;
      g += v;
      bz += v;
      l = l + 1;
      s++;
      bz = bz + y;
  }

}
