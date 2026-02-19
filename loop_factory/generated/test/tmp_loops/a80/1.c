int main1(int k,int n){
  int l, i, v, c;

  l=(k%20)+18;
  i=0;
  v=n;
  c=-1;

  while (i<l) {
      v = v+4;
      c = c+3;
      i = i+1;
  }

  while (c<v) {
      l = l+l;
      l = l-l;
      c = c+1;
  }

}
