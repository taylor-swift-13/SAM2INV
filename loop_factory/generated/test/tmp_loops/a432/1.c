int main1(int b,int k){
  int l, i, v;

  l=k;
  i=l;
  v=2;

  while (i>0) {
      v = v+v;
      v = v+1;
      i = i-1;
  }

  while (i<v) {
      l = l+1;
      i = i+1;
  }

}
