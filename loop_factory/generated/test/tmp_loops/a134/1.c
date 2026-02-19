int main1(int n,int q){
  int l, i, v, d;

  l=n;
  i=0;
  v=3;
  d=i;

  while (i<l) {
      v = v*3;
      d = d/3;
      v = v+d+d;
  }

  while (v<d) {
      v = v+1;
  }

}
