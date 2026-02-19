int main1(int k,int n){
  int l, i, v;

  l=(n%40)+11;
  i=l;
  v=n;

  while (i>0) {
      v = v+i;
      i = i-1;
  }

  while (v>0) {
      l = l-l;
      v = v-1;
  }

}
