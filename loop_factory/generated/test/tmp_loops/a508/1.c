int main1(int m,int n){
  int l, i, v;

  l=n+20;
  i=0;
  v=m;

  while (i<l) {
      v = v-v;
      v = v+1;
      i = i+2;
  }

  while (l<i) {
      l = l+1;
  }

}
