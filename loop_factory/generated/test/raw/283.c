int main1(int n,int q){
  int l, i, v;

  l=70;
  i=l;
  v=0;

  while (i>0) {
      v = v+v;
      i = i-1;
  }

  while (v>0) {
      i = i+v;
      v = v-1;
  }

  while (i<v) {
      l = l-l;
      i = i+4;
  }

}
