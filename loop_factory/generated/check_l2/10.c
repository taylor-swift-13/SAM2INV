int main10(int n,int p,int q){
  int c, x, y, z, z1, w, p1;

  c=0;
  x=0;
  y=1;
  z=6;
  z1=0;
  w=0;
  p1=0;

  while (c<=p) {
      c = c+1;
      x = x+y;
      y = y+z;
      z = z+6;
  }

  while (q>0) {
      z1 = z1+p*p;
      w = w+n*n;
      p1 = p1+p*n;
      q = q-1;
  }

}
