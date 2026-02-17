int main1(int m,int n,int p){
  int l, i, v, y, q, f;

  l=51;
  i=0;
  v=i;
  y=p;
  q=p;
  f=l;

  while (i<l) {
      v = v+i;
      y = y*y;
      q = q+v*y;
      v = v*v+y;
      i = i+1;
  }

}
