int main1(int b,int k){
  int l, i, v;

  l=k-3;
  i=l;
  v=k;

  while (i>0) {
      v = v-v;
      v = v+1;
      i = i-1;
  }

  while (v<i) {
      v = v+1;
  }

}
