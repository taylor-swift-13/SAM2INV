int main1(int n,int p){
  int l, i, v;

  l=p;
  i=0;
  v=n;

  while (i<l) {
      v = v-v;
      v = v+i;
      i = i+1;
  }

  while (l<i) {
      l = l+1;
  }

}
