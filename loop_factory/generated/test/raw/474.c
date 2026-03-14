int main1(int m){
  int st, ix, g3, j30n, e7;

  st=75;
  ix=0;
  g3=0;
  j30n=st;
  e7=0;

  while (1) {
      if (!(g3<=st-1)) {
          break;
      }
      j30n = g3;
      g3 += 4;
      e7 += g3;
  }

  while (1) {
      if (!(e7<ix)) {
          break;
      }
      e7 = e7 + 1;
      g3 = g3 + m;
      j30n += g3;
  }

}
