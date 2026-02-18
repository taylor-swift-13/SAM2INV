int main1(int k,int m,int n,int p){
  int l, i, v;

  l=m+10;
  i=0;
  v=-2;

  while (i<l) {
      if (i+4<=m+l) {
          v = v+1;
      }
      v = v-v;
      if (l<i+1) {
          v = v+1;
      }
      i = i+1;
  }

}
