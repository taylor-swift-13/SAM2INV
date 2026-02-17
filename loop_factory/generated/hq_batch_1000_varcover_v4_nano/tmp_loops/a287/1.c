int main1(int a,int m,int n,int p){
  int l, i, v, e, y, j, h;

  l=n+25;
  i=0;
  v=a;
  e=-1;
  y=-5;
  j=p;
  h=p;

  while (i<l) {
      v = v+i;
      e = e*e;
      y = y+v*e;
      if (i+4<=m+l) {
          y = e*e;
      }
      else {
          h = h*v;
      }
      i = i+1;
  }

}
