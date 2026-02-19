int main1(int k,int q){
  int l, i, v;

  l=q+10;
  i=0;
  v=k;

  while (i<l) {
      v = v-v;
      i = i+5;
  }

  while (l<v) {
      i = i+l;
      i = i-i;
      l = l+1;
  }

}
