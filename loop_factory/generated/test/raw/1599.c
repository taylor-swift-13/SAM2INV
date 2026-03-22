int main1(int m){
  int t, yp, tk, k, s, pa3, g, j3;

  t=111;
  yp=t;
  tk=3;
  k=3;
  s=0;
  pa3=3;
  g=0;
  j3=t;

  while (1) {
      if (!(yp<t)) {
          break;
      }
      if (yp%3==0) {
          if (tk>0) {
              tk -= 1;
              s++;
          }
      }
      else {
          if (tk<pa3) {
              tk++;
              k += 1;
          }
      }
      g++;
      j3 = j3 + 3;
      pa3 = pa3 + tk;
      yp += 1;
      pa3 = pa3+j3+m;
  }

}
