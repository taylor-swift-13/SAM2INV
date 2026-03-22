int main1(int m,int b){
  int p, dd, lmh;

  p=63;
  dd=(b%40)+2;
  lmh=0;

  while (dd!=lmh) {
      lmh = dd;
      dd = (dd+p/dd)/2;
      m = m+lmh-dd;
  }

}
