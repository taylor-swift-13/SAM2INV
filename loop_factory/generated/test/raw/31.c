int main1(int a){
  int bj, r, y;

  bj=a+12;
  r=0;
  y=bj;

  while (1) {
      if (!(r<bj)) {
          break;
      }
      y = y + 3;
      r = r + 1;
      a = a+bj-r;
  }

}
