int main1(int a,int n,int p){
  int l, i, v;

  l=75;
  i=l;
  v=i;

  while (i>0) {
      v = v-v;
      if (i+5<=n+l) {
          v = v-v;
      }
      else {
          v = v+v;
      }
      i = i-1;
  }

}
