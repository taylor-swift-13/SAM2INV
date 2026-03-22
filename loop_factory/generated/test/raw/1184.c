int main1(){
  int wca, gzgk, n, iq;

  wca=(1%28)+8;
  gzgk=(1%22)+5;
  n=0;
  iq=2;

  while (1) {
      if (!(gzgk!=0)) {
          break;
      }
      if (gzgk%2==1) {
          n = n + wca;
          gzgk--;
      }
      gzgk = gzgk/2;
      wca = 2*wca;
      iq = iq+(wca%5);
  }

}
