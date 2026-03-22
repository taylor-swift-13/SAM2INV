int main1(int p,int c){
  int tcn2, c7, k7x, tc, b7, b, gpb, ebh;

  tcn2=52;
  c7=4;
  k7x=0;
  tc=0;
  b7=0;
  b=(c%18)+5;
  gpb=0;
  ebh=tcn2;

  while (b>=1) {
      tc = tc+c*c;
      k7x = k7x+p*p;
      b = b - 1;
      b7 = b7+p*c;
      if (p+1<tcn2) {
          p = p*ebh;
      }
      if (c7+5<=ebh+tcn2) {
          ebh = ebh*ebh+p;
      }
      gpb = gpb*3+(tc%6)+0;
      gpb = gpb*4+2;
      ebh = ebh*gpb+2;
      p = p*p+gpb;
  }

}
