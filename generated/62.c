int main62(int i){
  int fu, yq7, e92, e, o, pc, w9, ehw;

  fu=31;
  yq7=fu;
  e92=0;
  e=(i%28)+10;
  o=0;
  pc=8;
  w9=i;
  ehw=yq7;

  while (1) {
      if (!(e>e92)) {
          break;
      }
      e -= e92;
      e92++;
      pc = pc + 3;
      ehw = ehw + yq7;
      w9 = w9+fu-yq7;
      o = o + yq7;
      while (yq7>0) {
          ehw = ehw+i*i;
          e92 = e92+i*i;
          yq7 -= 1;
          o = o+i*i;
          i = i + yq7;
      }
      while (1) {
          if (!(w9<e)) {
              break;
          }
          o = o/2;
          ehw = ehw*2;
          if (ehw+5<e) {
              ehw = ehw*2;
          }
          else {
              pc = o+w9;
          }
          ehw = ehw*ehw+i;
          w9 += 8;
      }
  }

}
