int main1(int m,int n){
  int l, i, v, r;

  l=76;
  i=0;
  v=l;
  r=l;

  while (i<l) {
      v = v+1;
      r = r+1;
      r = r+r;
  }

  while (i<v) {
      l = l+r;
      l = l+l;
      i = i+1;
  }

}
