int main3(int n,int p,int q){
  int x, y, c, i, j, x1, y1;

  x=1;
  y=p;
  c=1;
  i=0;
  j=0;
  x1=0;
  y1=1;

  while (c<q) {
      c = c+1;
      x = x*p+1;
      y = y*p;
  }

  while (i<q) {
      j = 0;
      while (j<n) {
          x1 = x1+y1;
          y1 = y1+1;
          j = j+1;
      }
      i = i+1;
  }

}
