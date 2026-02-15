int main20(int a,int b,int m){
  int x, y, c, x1, y1, c1;

  x=1;
  y=m;
  c=1;
  x1=1;
  y1=b;
  c1=1;

  while (c<a) {
      c = c+1;
      x = x*m+1;
      y = y*m;
      while (c1<m) {
          c1 = c1+1;
          x1 = x1*b+1;
          y1 = y1*b;
      }
  }

}
