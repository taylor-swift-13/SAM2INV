int main15(int b,int n,int p){
  int x, y, c, x1, y1, y2, x2, c1, y3, x3, c2;

  x=1;
  y=b;
  c=1;
  x1=p;
  y1=n;
  y2=0;
  x2=0;
  c1=0;
  y3=0;
  x3=0;
  c2=0;

  while (c<n) {
      c = c+1;
      x = x*b+1;
      y = y*b;
  }

  while (x1!=0&&y1!=0) {
      if (x1>y1) {
          x1 = x1-y1;
      }
      else {
          y1 = y1-x1;
      }
  }

  while (c1<p) {
      c1 = c1+1;
      y2 = y2+1;
      x2 = y2*y2*y2+x2;
  }

  while (c2<b) {
      c2 = c2+1;
      y3 = y3+1;
      x3 = y3+x3;
  }

}
