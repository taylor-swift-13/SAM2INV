int main1(int n,int g){
  int v, fy8, w0, tp, jx5, h, hc, dm, cd, eu5;

  v=13;
  fy8=0;
  w0=0;
  tp=0;
  jx5=0;
  h=0;
  hc=0;
  dm=0;
  cd=0;
  eu5=2;

  while (w0<v) {
      if (!(!(w0%8==0))) {
          if (w0%7==0) {
              jx5 = jx5 + 1;
          }
          else {
              if (w0%2==0) {
                  h += 1;
              }
              else {
                  if (1) {
                      hc += 1;
                  }
              }
          }
      }
      else {
          tp = tp + 1;
      }
      w0 += 1;
      eu5 += 2;
      cd = cd+w0%8;
      n = n + cd;
      dm += 1;
      eu5 -= 1;
      eu5 = eu5 + fy8;
  }

}
