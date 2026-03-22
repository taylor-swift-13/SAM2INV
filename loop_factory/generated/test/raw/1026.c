int main1(){
  int j1x, p, m, tmdw;

  j1x=1+4;
  p=0;
  m=0;
  tmdw=p;

  while (m<j1x) {
      tmdw = j1x-m;
      tmdw += p;
      m++;
  }

  while (1) {
      tmdw = tmdw + 1;
      if (tmdw>=m) {
          break;
      }
  }

}
