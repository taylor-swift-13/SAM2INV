int main1(int k,int m,int p){
  int l, i, v;

  l=56;
  i=0;
  v=m;

  while (i<l) {
      if (i+6<=m+l) {
          v = v-v;
      }
      v = v+i;
      v = v-v;
      v = v+6;
      i = i+1;
  }

}
