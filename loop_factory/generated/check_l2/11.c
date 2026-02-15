int main11(int k,int m,int q){
  int x, y, c, x1, y1, z;

  x=1;
  y=q;
  c=1;
  x1=k;
  y1=q;
  z=0;

  while (c<m) {
      c = c+1;
      x = x*q+1;
      y = y*q;
  }

  while (y1!=0) {
      if (y1%2==1) {
          z = z+x1;
          y1 = y1-1;
      }
      x1 = 2*x1;
      y1 = y1/2;
  }

}
