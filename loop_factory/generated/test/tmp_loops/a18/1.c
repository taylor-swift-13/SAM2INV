int main1(int b,int n){
  int l, i, v;

  l=b+13;
  i=l;
  v=n;

  while (i>0) {
      v = v+i;
      i = i-1;
  }

  while (v>0) {
      l = l+v;
      v = v-1;
  }

}
