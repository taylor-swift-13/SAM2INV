int main1(int k,int m,int n,int p){
  int l, i, v;

  l=n;
  i=0;
  v=n;

  while (i<l) {
      v = v-v;
      if (v+1<l) {
          v = v+1;
      }
      if (p<l+1) {
          v = v+1;
      }
      if (v+2<l) {
          v = v-v;
      }
      i = i+1;
  }

}
