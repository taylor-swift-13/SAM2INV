int main1(int a,int q){
  int l, i, v, u;

  l=q;
  i=0;
  v=1;
  u=l;

  while (i<l) {
      v = v+u+u;
      i = i+1;
  }

  while (v<i) {
      l = l+l;
      v = v+1;
  }

}
