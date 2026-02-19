int main1(int n,int q){
  int l, i, v, b;

  l=q+22;
  i=0;
  v=i;
  b=n;

  while (i<l) {
      v = v+b+b;
      v = v+1;
      i = i+1;
  }

  while (b<i) {
      b = b+1;
  }

}
