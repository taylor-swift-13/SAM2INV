int main1(int d,int a,int x){
  int c, rf1, tb;

  c=d*4;
  rf1=0;
  tb=-8;

  while (1) {
      tb = tb + rf1;
      rf1++;
      if (rf1>=c) {
          break;
      }
  }

}
