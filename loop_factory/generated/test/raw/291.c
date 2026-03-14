int main1(int n){
  int dh, d, ln, pl, ttir;

  dh=n*4;
  d=4;
  ln=0;
  pl=d;
  ttir=n;

  while (d<=dh-1) {
      pl = pl + ttir;
      ttir += ln;
      pl += d;
      d++;
  }

}
