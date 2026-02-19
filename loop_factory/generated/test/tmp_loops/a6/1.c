int main1(int n,int q){
  int l, i, v;

  l=q+8;
  i=0;
  v=2;

  while (i<l) {
      v = v+1;
      v = q-v;
      i = i+1;
  }

  while (l>0) {
      i = i+1;
      l = l-1;
  }

}
