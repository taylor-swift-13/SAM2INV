int main1(int t){
  int a, ph, y9q, itp, v;

  a=(t%25)+8;
  ph=0;
  y9q=1;
  itp=5;
  v=-4;

  while (1) {
      if (!(y9q<=a)) {
          break;
      }
      itp = itp+y9q*y9q;
      v += ph;
      y9q = y9q + 1;
  }

  while (a<itp) {
      y9q = itp-a;
      t += v;
      a++;
  }

}
