int main1(int m,int p){
  int l, i, v;

  l=(p%31)+20;
  i=0;
  v=i;

  while (i<l) {
      v = v-v;
      v = v+4;
      i = i+1;
  }

  while (l>0) {
      l = l-1;
  }

}
