int main1(int r){
  int mw, jxa, j, yqp, xy, yk8, h;

  mw=48;
  jxa=-6;
  j=0;
  yqp=0;
  xy=0;
  yk8=5;
  h=0;

  while (jxa<mw) {
      if (jxa%3==0) {
          if (j>0) {
              j -= 1;
              xy++;
          }
      }
      else {
          if (j<yk8) {
              j++;
              yqp++;
          }
      }
      h += 1;
      jxa += 1;
      r += h;
  }

}
