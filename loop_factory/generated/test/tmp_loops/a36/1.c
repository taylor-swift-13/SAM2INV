int main1(int n){
  int h, b6, b0, mu, mi;

  h=n-2;
  b6=h;
  b0=0;
  mu=b6;
  mi=0;

  while (b0<h) {
      mu = b0+4;
      n = n+h-b6;
      b0 += 2;
  }

  while (mu>=1) {
      mi = mi+h*mu;
      b6 += mu;
      mu = =1;
  }

}
