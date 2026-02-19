int main1(int k,int q){
  int l, i, v;

  l=q+3;
  i=l;
  v=q;

  while (i>0) {
      v = v+v;
      v = v-v;
      i = i-1;
  }

  while (i>0) {
      l = l+5;
      l = l+l;
      i = i-1;
  }

}
