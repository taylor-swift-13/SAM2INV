int main1(int d,int t){
  int l, ieg, dj6, aj, x, et, blu, e6, l1f, avf;

  l=t+20;
  ieg=0;
  dj6=0;
  aj=0;
  x=0;
  et=d;
  blu=5;
  e6=0;
  l1f=l;
  avf=d;

  while (1) {
      if (!(ieg<l)) {
          break;
      }
      aj += 1;
      x = x + 1;
      if (aj>=4) {
          aj -= 4;
          dj6 += 1;
      }
      ieg = ieg + 1;
      if ((ieg%2)==0) {
          e6 = e6-(-8);
      }
      et++;
      l1f += 2;
      avf += x;
      blu = blu + et;
      avf += 1;
  }

}
