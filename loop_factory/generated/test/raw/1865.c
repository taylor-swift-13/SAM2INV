int main1(int n,int m){
  int zup, zq, lva, gvn, d29, g0, u, w;

  zup=166;
  zq=1;
  lva=0;
  gvn=1;
  d29=0;
  g0=0;
  u=zup;
  w=3;

  while (1) {
      if (!(lva>=0&&lva<3)) {
          break;
      }
      if (lva==0&&gvn>=zup) {
          lva = 3;
      }
      else {
          if (lva==1&&d29<gvn) {
              g0 = g0+gvn-d29;
              d29 = d29 + 1;
          }
          else {
              if (lva==1&&d29>=gvn) {
                  lva = 2;
              }
              else {
                  if (lva==2) {
                      gvn++;
                      lva = 0;
                  }
              }
          }
      }
      u = u+(zq%2);
      m++;
      m++;
      u = u + 1;
      w = w - 1;
      m += 6;
  }

}
