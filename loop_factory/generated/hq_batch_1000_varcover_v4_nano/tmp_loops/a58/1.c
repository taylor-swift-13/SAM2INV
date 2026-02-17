int main1(int a,int k,int n,int q){
  int l, i, v, y, r, g;

  l=(a%38)+9;
  i=l;
  v=-2;
  y=l;
  r=1;
  g=0;

  while (i>0) {
      v = v*3;
      y = y/3;
      r = r+a;
      g = g%5;
      i = i/2;
  }

}
