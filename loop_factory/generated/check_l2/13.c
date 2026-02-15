int main13(int a,int m,int q){
  int x, y, c, c1, x1, y1, z;

  x=1;
  y=q;
  c=1;
  c1=0;
  x1=0;
  y1=1;
  z=6;

  while (c<a) {
      c = c+1;
      x = x*q+1;
      y = y*q;
  }

  while (c1<=q) {
      c1 = c1+1;
      x1 = x1+y1;
      y1 = y1+z;
      z = z+6;
  }

}
