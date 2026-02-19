int main1(int n,int q){
  int l, i, v;

  l=(n%14)+7;
  i=0;
  v=n;

  while (i<l) {
      v = v-v;
      i = i+1;
  }

  while (v>0) {
      v = v-1;
  }

}
