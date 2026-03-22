int main1(int b,int z){
  int n, o9, y, cnc, i;

  n=z*5;
  o9=n;
  y=0;
  cnc=5;
  i=b;

  while (1) {
      if (!(o9>1)) {
          break;
      }
      y = y*4;
      cnc = cnc/4;
      i = i*3+(y%5)+3;
      o9 = 1;
  }

}
