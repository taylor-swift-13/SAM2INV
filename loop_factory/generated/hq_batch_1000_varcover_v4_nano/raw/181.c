int main1(int k,int m,int n){
  int l, i, v;

  l=61;
  i=0;
  v=k;

  while (i<l) {
      v = v-v;
      if (k<i+1) {
          v = v+v;
      }
      v = v+v;
      v = v+1;
      if (v+3<l) {
          v = v-v;
      }
      i = i+1;
  }

}
