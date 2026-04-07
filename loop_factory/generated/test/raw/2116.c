int main1(int a){
  int a7, q, wj, fh, f;

  a7=a+21;
  q=0;
  wj=1;
  fh=0;
  f=-3;

  while (q < a7) {
      f = (wj += (q < a7/2 ? a : -a), fh -= (q < a7/2 ? a : -a), ++q);
      wj = wj+f-f;
      q = a7;
  }

}
