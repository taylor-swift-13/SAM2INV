int main1(int m,int q){
  int l, i, v;

  l=63;
  i=0;
  v=l;

  while (i<l) {
      v = v-v;
      v = v+i;
      i = i+5;
  }

  while (l<i) {
      l = l+3;
  }

}
