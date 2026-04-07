int main1(int m){
  int vl, bw, f1g, yf, k5, lf, ff, l3;

  vl=(m%18)+6;
  bw=0;
  f1g=0;
  yf=0;
  k5=0;
  lf=0;
  ff=0;
  l3=0;

  while (f1g<vl) {
      if (f1g%6==0) {
          yf++;
          l3 = l3 + 1;
      }
      else {
          if (f1g%5==0) {
              k5++;
              l3 += 2;
          }
          else {
              if (f1g%3==0) {
                  lf = lf + 1;
                  l3 = l3 + 3;
              }
              else {
                  if (1) {
                      ff = ff + 1;
                      l3 += 4;
                  }
              }
          }
      }
      f1g += 1;
      m += vl;
      m = m + bw;
  }

}
