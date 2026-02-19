int main1(int p,int q){
  int l, i, v, b;

  l=22;
  i=0;
  v=i;
  b=i;

  while (i<l) {
      v = v+1;
      b = b+v;
      i = i+1;
  }

  while (l>0) {
      v = v*4;
      b = b/4;
  }

}
