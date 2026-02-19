int main1(int k,int n){
  int l, i, v;

  l=54;
  i=0;
  v=n;

  while (i<l) {
      v = l-k;
      v = k-i;
      i = i+5;
  }

  while (l>0) {
      v = v-n;
      v = v+v;
      l = l-1;
  }

}
