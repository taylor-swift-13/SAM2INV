int main1(){
  int l50, xi1m, wg, y, mu, m8, t5w4, n, caxo, th;

  l50=(1%12)+11;
  xi1m=0;
  wg=8;
  y=0;
  mu=0;
  m8=l50;
  t5w4=11;
  n=12;
  caxo=-5;
  th=8;

  while (xi1m < l50) {
      if ((xi1m % 2) == 0) {
          wg = wg + 1;
          y++;
      }
      else {
          wg--;
          y -= 1;
      }
      xi1m += 1;
      if (!(!(caxo<n+1))) {
          n = n + 3;
      }
      mu += wg;
      th++;
      m8 += wg;
      t5w4 = t5w4 + y;
      mu++;
      m8 += mu;
  }

}
