int main1(int k,int n){
  int y, hk, d1mr, my1;

  y=(k%6)+7;
  hk=0;
  d1mr=1;
  my1=1;

  while (1) {
      if (!(hk<y)) {
          break;
      }
      d1mr += 4;
      my1 += 4;
      hk += 4;
      k = k + hk;
      k += 2;
  }

}
