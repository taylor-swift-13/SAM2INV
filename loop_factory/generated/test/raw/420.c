int main1(){
  int gx, oa, t, nnm, h5, g;

  gx=158;
  oa=gx;
  t=0;
  nnm=0;
  h5=0;
  g=6;

  while (oa<=gx-1) {
      nnm = oa%5;
      if (oa>=g) {
          h5 = (oa-g)%5;
          t = t+nnm-h5;
      }
      else {
          t = t + nnm;
      }
      oa++;
      g += t;
  }

}
