int main1(int n,int q){
  int l, i, v, d;

  l=n;
  i=0;
  v=n;
  d=i;

  while (i<l) {
      v = v+d+d;
      v = v+1;
      i = i+4;
  }

  while (i>0) {
      l = l+1;
      i = i-1;
  }

}
