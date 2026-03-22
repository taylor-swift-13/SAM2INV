int main1(){
  int cj2, qd, rp, tdt, mu, n;

  cj2=1+24;
  qd=0;
  rp=(1%28)+8;
  tdt=(1%22)+5;
  mu=0;
  n=cj2;

  while (tdt!=0) {
      if (tdt%2==1) {
          mu += rp;
          tdt = tdt - 1;
      }
      tdt = tdt/2;
      rp = 2*rp;
      n = n + qd;
      n = n*n+n;
  }

}
