int main7(int k,int n,int q){
  int x, x1, y, c, c1;

  x=q;
  x1=1;
  y=q;
  c=1;
  c1=0;

  while (x>0) {
      x = x-1;
  }

  while (c<n) {
      c = c+1;
      x1 = x1*q+1;
      y = y*q;
  }

  while (c1<19) {
      n = n+7;
      q = q+7;
      c1 = c1+1;
  }

}
