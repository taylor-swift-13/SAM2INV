int main1(int a,int k,int m){
  int c, x, y, z, x1, y1, z1;

  c=0;
  x=0;
  y=1;
  z=6;
  x1=m;
  y1=k;
  z1=0;

  while (c<=m) {
      c = c+1;
      x = x+y;
      y = y+z;
      z = z+6;
  }

  while (y1!=0) {
      if (y1%2==1) {
          z1 = z1+x1;
          y1 = y1-1;
      }
      x1 = 2*x1;
      y1 = y1/2;
  }

}
