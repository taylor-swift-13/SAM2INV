int main5(int k,int n,int q){
  int i, j, x, y, x1, y1, z;

  i=0;
  j=0;
  x=0;
  y=1;
  x1=q;
  y1=n;
  z=0;

  while (i<k) {
      j = 0;
      while (j<q) {
          x = x+y;
          y = y+1;
          j = j+1;
      }
      i = i+1;
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
