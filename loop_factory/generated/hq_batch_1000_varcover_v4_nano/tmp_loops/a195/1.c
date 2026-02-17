int main1(int a,int b,int k,int p){
  int l, i, v, g, x, y;

  l=a+8;
  i=0;
  v=(a%60)+60;
  g=(a%9)+2;
  x=0;
  y=0;

  while (v>g*x+y) {
      if (y==g-1) {
          y = 0;
          x = x+1;
      }
      else {
          y = y+1;
      }
      y = y*y+v;
  }

}
