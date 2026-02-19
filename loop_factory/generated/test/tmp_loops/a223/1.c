int main1(int a,int m){
  int l, i, v;

  l=13;
  i=0;
  v=a;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (l<i) {
      v = v-v;
      v = v+1;
      l = l+1;
  }

}
