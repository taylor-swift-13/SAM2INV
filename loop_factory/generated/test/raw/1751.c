int main1(){
  int gcc, d8, hg, hx, kx;

  gcc=1;
  d8=0;
  hg=d8;
  hx=-3;
  kx=gcc;

  while (d8 < gcc) {
      hg += hx;
      d8 = d8 + 1;
      hx += 1;
      kx = kx+(hg%3);
  }

}
