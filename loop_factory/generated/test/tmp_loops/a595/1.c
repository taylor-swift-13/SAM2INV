int main1(int b,int p){
  int l, i, v, y;

  l=14;
  i=0;
  v=-4;
  y=b;

  while (i<l) {
      y = y+y;
      y = y+v;
      i = i+1;
  }

  while (y<v) {
      y = y+2;
  }

}
