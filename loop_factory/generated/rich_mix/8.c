int main8(int a,int m,int q){
  int x, y, c, x1, y1, c1, x2;

  x=1;
  y=a;
  c=1;
  x1=a;
  y1=m;
  c1=0;
  x2=m;

  while (c<q) {
      c = c+1;
      x = x*a+1;
      y = y*a;
  }

  while (x1!=0&&y1!=0) {
      if (x1>y1) {
          x1 = x1-y1;
      }
      else {
          y1 = y1-x1;
      }
  }

  while (c1<18) {
      q = q+8;
      m = m+8;
      c1 = c1+1;
  }

  while (x2>0) {
      x2 = x2-1;
  }

}
