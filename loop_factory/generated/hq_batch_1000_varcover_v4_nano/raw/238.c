int main1(int m,int n,int p){
  int l, i, v, x, t, y, s;

  l=(m%6)+9;
  i=l;
  v=n;
  x=i;
  t=n;
  y=-5;
  s=p;

  while (i>0) {
      v = v+4;
      t = t+1;
      t = t+1;
      y = s-y;
      if (v<v+1) {
          x = x+1;
      }
      i = i-1;
  }

}
