int main1(int a,int m){
  int v, d, y;

  v=a;
  d=0;
  y=m;

  while (d<v) {
      y = y+4;
      if ((d%5)==0) {
          y = y+y;
      }
  }

}
