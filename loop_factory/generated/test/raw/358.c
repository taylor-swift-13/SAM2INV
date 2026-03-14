int main1(){
  int ka, v5, w8, hbf, lev;

  ka=1;
  v5=0;
  w8=(1%28)+10;
  hbf=ka;
  lev=1*4;

  while (w8>v5) {
      w8 = w8 - v5;
      v5 = v5 + 1;
      hbf = hbf + w8;
      hbf = hbf*3+1;
      lev = (1)+(lev*hbf);
  }

  for (; w8-1>=0; w8 -= 1) {
  }

}
