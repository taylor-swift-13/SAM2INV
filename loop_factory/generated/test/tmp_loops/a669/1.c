int main1(int k,int m){
  int l, i, v, n;

  l=61;
  i=0;
  v=-2;
  n=3;

  while (i<l) {
      v = v+n+n;
      i = i+3;
  }

  while (l<i) {
      n = n+v+v;
      l = l+1;
  }

}
