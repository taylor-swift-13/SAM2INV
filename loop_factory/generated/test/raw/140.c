int main1(int o,int y){
  int cpqr, fq, fh;

  cpqr=77;
  fq=cpqr;
  fh=0;

  while (fq<cpqr) {
      if (fq%2==0) {
          if (fh>0) {
              fh = fh - 1;
              fh += 1;
          }
      }
      else {
          if (fh>0) {
              fh = fh - 1;
              fh += 1;
          }
      }
      fq += 1;
      o += fh;
      o = o+y+y;
  }

}
