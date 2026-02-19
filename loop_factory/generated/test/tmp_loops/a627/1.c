int main1(int n,int q){
  int l, i, v;

  l=q+8;
  i=0;
  v=q;

  while (i<l) {
      v = v-v;
      i = i+1;
  }

  while (i<v) {
      l = l+1;
      l = l+l;
      i = i+1;
  }

}
