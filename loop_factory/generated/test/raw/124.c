int main1(int b,int i){
  int xy, st, tudf, a8;

  xy=i;
  st=0;
  tudf=1;
  a8=1;

  while (st<xy) {
      if (tudf>=8) {
          a8 = -1;
      }
      if (tudf<=1) {
          a8 = 1;
      }
      tudf = tudf + a8;
      st = st + 1;
      b = b + tudf;
  }

}
