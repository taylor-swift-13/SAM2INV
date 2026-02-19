int main1(int k,int n){
  int l, i, v;

  l=(n%25)+17;
  i=l;
  v=n;

  while (i>0) {
      i = i/2;
  }

  while (v>0) {
      l = l-l;
      l = l+1;
      v = v-1;
  }

}
