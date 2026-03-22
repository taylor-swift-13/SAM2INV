int main1(int i){
  int n, nd, x, dd0, rk6, g2eg, j, a20, yn;

  n=i+8;
  nd=0;
  x=1;
  dd0=1;
  rk6=1;
  g2eg=1;
  j=-3;
  a20=i+1;
  yn=nd;

  while (1) {
      if (!(rk6<=n)) {
          break;
      }
      x = x*(i/rk6);
      if ((rk6/2)%2==0) {
          g2eg = 1;
      }
      else {
          g2eg = -1;
      }
      dd0 = dd0+g2eg*x;
      rk6 += 1;
      x = x*(i/rk6);
      if (a20+4<n) {
          a20 = a20*2;
      }
      yn = yn+(x%2);
      i = i+rk6+g2eg;
      j = j+dd0+dd0;
      j = j*4;
  }

}
