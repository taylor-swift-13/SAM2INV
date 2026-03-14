int main1(int t){
  int gx, g, f4sd, v9, ndj;

  gx=56;
  g=gx;
  f4sd=38;
  v9=1;
  ndj=0;

  while (1) {
      if (!(f4sd>0&&v9<=gx)) {
          break;
      }
      if (!(f4sd<=v9)) {
          f4sd = 0;
      }
      else {
          f4sd = f4sd - v9;
      }
      g++;
      ndj++;
      v9++;
  }

}
