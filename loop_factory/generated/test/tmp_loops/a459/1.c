int main1(int b,int m){
  int l, i, v;

  l=m;
  i=0;
  v=b;

  while (i<l) {
      v = v+v;
      v = v+1;
      i = i+3;
  }

  while (l<v) {
      l = l+1;
  }

}
