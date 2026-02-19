int main1(int m,int n){
  int l, i, v, u;

  l=(m%28)+20;
  i=l;
  v=4;
  u=m;

  while (i>0) {
      v = v+1;
      u = u+1;
      u = u+u;
  }

  while (v<i) {
      u = u+l+l;
      u = u+1;
      v = v*2;
  }

}
