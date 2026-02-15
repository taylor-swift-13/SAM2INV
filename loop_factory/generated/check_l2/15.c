int main15(int k,int m,int p){
  int x, y, c, x1, y1, c1;

  x=1;
  y=p;
  c=1;
  x1=1;
  y1=p;
  c1=1;

  while (c<m) {
      c = c+1;
      x = x*p+1;
      y = y*p;
      while (c1<m) {
          c1 = c1+1;
          x1 = x1*p+1;
          y1 = y1*p;
      }
  }

}
