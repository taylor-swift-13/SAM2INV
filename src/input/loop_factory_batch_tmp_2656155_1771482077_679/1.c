int main1(int n,int q){
  int l, i, v, b;

  l=q-7;
  i=1;
  v=l;
  b=i;

  while (i<l) {
      v = v*2;
      b = b/2;
  }

  while (l<i) {
      b = b+1;
      v = v+b;
      l = l+1;
  }

}
