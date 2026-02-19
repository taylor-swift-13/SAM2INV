int main1(int m,int q){
  int l, i, v;

  l=q;
  i=0;
  v=3;

  while (i<l) {
      v = v+2;
      v = v-v;
      i = i+1;
  }

  while (v<i) {
      l = l+v;
      v = v+1;
  }

}
