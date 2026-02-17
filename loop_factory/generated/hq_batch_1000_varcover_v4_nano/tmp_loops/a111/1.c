int main1(int b,int m,int n,int q){
  int l, i, v, j, y, x, p, z, u, e;

  l=q;
  i=0;
  v=(q%20)+1;
  j=(q%25)+1;
  y=0;
  x=b;
  p=n;
  z=m;
  u=m;
  e=l;

  while (j!=0) {
      if (j%2==1) {
          y = y+v;
          j = j-1;
      }
      else {
      }
      v = 2*v;
      j = j/2;
  }

}
