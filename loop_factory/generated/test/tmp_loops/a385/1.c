int main1(int m,int n){
  int l, i, v, r;

  l=18;
  i=0;
  v=2;
  r=n;

  while (i<l) {
      v = v*2;
      r = r/2;
      v = v+1;
  }

  while (v<r) {
      i = i-i;
      i = i+r;
      v = v+1;
  }

}
