int main1(int f,int u){
  int t5, vd, h, ltp;

  t5=u*5;
  vd=t5;
  h=0;
  ltp=0;

  while (1) {
      if (!(ltp<t5)) {
          break;
      }
      h = (h+1)%3;
      ltp = ltp + 1;
      f += vd;
      f += 4;
  }

}
