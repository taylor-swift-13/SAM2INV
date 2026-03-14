int main1(int t,int w){
  int rw9, jo8, i, x0, t45, yxgi;

  rw9=181;
  jo8=rw9;
  i=28;
  x0=0;
  t45=1;
  yxgi=0;

  while (1) {
      if (!(i>0&&jo8<rw9)) {
          break;
      }
      if (i<=t45) {
          yxgi = i;
      }
      else {
          yxgi = t45;
      }
      t45 += 1;
      x0 = x0 + yxgi;
      i = i - yxgi;
      jo8 = jo8 + 1;
  }

}
