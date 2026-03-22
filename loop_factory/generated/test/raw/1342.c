int main1(int i,int s){
  int ks, c, t, t6, yn;

  ks=10;
  c=2;
  t=0;
  t6=(i%28)+10;
  yn=c;

  while (1) {
      if (!(t6>t)) {
          break;
      }
      t6 -= t;
      yn = (ks-c)+(yn);
      t += 1;
  }

}
