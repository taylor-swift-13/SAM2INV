int main1(int a,int m){
  int l, i, v;

  l=40;
  i=0;
  v=m;

  while (i<l) {
      v = v+1;
      i = i+1;
  }

  while (i<v) {
      l = l+i;
      l = l+1;
      i = i+4;
  }

}
