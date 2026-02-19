int main1(int k,int m){
  int l, i, v;

  l=(k%40)+12;
  i=0;
  v=m;

  while (i<l) {
      v = v-v;
      i = i+1;
  }

  while (l<i) {
      v = v+l;
      v = v-v;
      l = l+1;
  }

}
