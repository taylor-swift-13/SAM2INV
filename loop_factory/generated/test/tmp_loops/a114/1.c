int main1(int k,int p){
  int l, i, v;

  l=(k%35)+14;
  i=l;
  v=i;

  while (i>0) {
      v = v-v;
      v = v+v;
      i = i-1;
  }

  while (l>0) {
      l = l-1;
  }

}
