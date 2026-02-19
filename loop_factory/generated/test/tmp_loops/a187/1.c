int main1(int b,int k){
  int l, i, v;

  l=32;
  i=0;
  v=i;

  while (i<l) {
      v = v+1;
      v = v+i;
      i = i+1;
  }

  while (l<i) {
      v = v+l;
      l = l+1;
  }

}
