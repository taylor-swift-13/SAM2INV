int main1(int r){
  int nx, i, s6l, sj;

  nx=(r%22)+10;
  i=0;
  s6l=r;
  sj=0;

  while (i+1<=nx) {
      s6l = s6l + i;
      sj = sj*sj;
      i = i + 1;
  }

}
