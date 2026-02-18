int main1(int a,int n,int p,int q){
  int l, i, v;

  l=40;
  i=0;
  v=q;

  while (i<l) {
      if (v+5<l) {
          v = v+i;
      }
      else {
          v = v-v;
      }
      if (v+5<l) {
          v = v-v;
      }
      i = i+1;
  }

}
