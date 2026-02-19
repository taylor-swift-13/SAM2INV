int main1(int b,int m){
  int l, i, v;

  l=b;
  i=0;
  v=b;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (i<v) {
      l = l+1;
      l = l+l;
      i = i*3;
  }

}
