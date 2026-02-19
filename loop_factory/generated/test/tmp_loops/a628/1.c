int main1(int n,int p){
  int l, i, v, u;

  l=n+23;
  i=l;
  v=-2;
  u=l;

  while (i>0) {
      v = v+1;
      u = u-1;
  }

  while (v>0) {
      u = u*4;
      l = l/4;
      u = u+1;
  }

}
