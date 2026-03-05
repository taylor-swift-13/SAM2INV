int main1(int n){
  int fjqt, fv, y68v, p6;

  fjqt=54;
  fv=0;
  y68v=5;
  p6=0;

  while (fv<fjqt) {
      p6 = fv%5;
      if (fv>=y68v) {
          y68v = (fv-y68v)%5;
          y68v = y68v+p6-y68v;
      }
      else {
          y68v += p6;
      }
      fv++;
      n += p6;
  }

}
