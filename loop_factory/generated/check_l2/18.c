int main18(int b,int m,int n){
  int x, y, z, x1, y1, c;

  x=n;
  y=b;
  z=0;
  x1=1;
  y1=n;
  c=1;

  while (y!=0) {
      if (y%2==1) {
          z = z+x;
          y = y-1;
      }
      x = 2*x;
      y = y/2;
      while (c<m) {
          c = c+1;
          x1 = x1*n+1;
          y1 = y1*n;
      }
  }

}
