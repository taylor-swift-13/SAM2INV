int main4(int a,int m,int p){
  int c, x, y, z, z1, w, p1;

  c=0;
  x=0;
  y=1;
  z=6;
  z1=0;
  w=0;
  p1=0;

  while (c<=m) {
      c = c+1;
      x = x+y;
      y = y+z;
      z = z+6;
      while (p>0) {
          z1 = z1+m*m;
          w = w+a*a;
          p1 = p1+m*a;
          p = p-1;
      }
  }

}
