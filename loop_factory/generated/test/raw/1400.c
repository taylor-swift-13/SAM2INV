int main1(){
  int st, xr2, ufa, y81, d, q1n, kx4;

  st=1*3;
  xr2=st;
  ufa=xr2;
  y81=xr2;
  d=0;
  q1n=5;
  kx4=xr2;

  while (1) {
      if (q1n>st) {
          break;
      }
      ufa += y81;
      y81 += d;
      q1n += 1;
      d += 6;
      kx4 = kx4+(d%2);
  }

}
