int main1(int k,int q){
  int l, i, v;

  l=(q%35)+6;
  i=l;
  v=k;

  while (i>0) {
      v = v+v;
      v = v+4;
      i = i-1;
  }

  while (l<i) {
      v = v+1;
      v = v-v;
      l = l+5;
  }

}
