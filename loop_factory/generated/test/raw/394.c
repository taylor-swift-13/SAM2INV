int main1(){
  int e8, pb, nls, m, u93d;

  e8=(1%15)+15;
  pb=0;
  nls=0;
  m=0;
  u93d=0;

  while (1) {
      if (!(pb<=e8-1)) {
          break;
      }
      u93d++;
      m++;
      if (m>=5) {
          m = m - 5;
          nls = nls + 1;
      }
      pb = pb + 1;
  }

}
