int main1(int k,int q){
  int l, i, v, p;

  l=q+3;
  i=0;
  v=i;
  p=k;

  while (i<l) {
      v = v*4;
      p = p/4;
      v = v+1;
  }

  while (p<i) {
      l = l+1;
      p = p+1;
  }

}
