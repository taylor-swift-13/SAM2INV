int main1(int a,int m){
  int l, i, v;

  l=m;
  i=0;
  v=l;

  while (i<l) {
      v = v+1;
      v = v+v;
      i = i+4;
  }

  while (l<i) {
      v = v+v;
      l = l+1;
  }

}
