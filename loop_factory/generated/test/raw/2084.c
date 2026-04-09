int main1(){
  int j, cj, l, wbh;

  j=1;
  cj=0;
  l=8;
  wbh=-3;

  while (1) {
      if (!(cj < j)) {
          break;
      }
      cj++;
      l = l + wbh;
      wbh = wbh+j-cj;
  }

}
