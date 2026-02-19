int main1(int a,int k){
  int l, i, v;

  l=k;
  i=0;
  v=k;

  while (i<l) {
      v = v+v;
      i = i+4;
  }

  while (l<i) {
      v = v+1;
      l = l+1;
  }

}
