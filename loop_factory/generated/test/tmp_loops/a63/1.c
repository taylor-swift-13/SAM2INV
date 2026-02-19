int main1(int k,int n){
  int l, i, v;

  l=k+13;
  i=l;
  v=2;

  while (i>0) {
      v = v+1;
      i = i-1;
  }

  while (l>0) {
      v = v-v;
      l = l-1;
  }

}
