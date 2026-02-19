int main1(int n,int p){
  int l, i, v;

  l=n-2;
  i=0;
  v=n;

  while (i<l) {
      v = v+i;
      i = i+5;
  }

  while (v>0) {
      l = l+l;
      v = v-1;
  }

}
