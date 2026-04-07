int main1(int l){
  int ich, f5, dc, xzw;

  ich=l+16;
  f5=0;
  dc=11;
  xzw=-3;

  while (1) {
      if (f5>=ich) {
          break;
      }
      f5 += 1;
      dc += 2;
      xzw = xzw+ich-f5;
      xzw++;
  }

}
