int main1(int n,int q){
  int l, i, v, o;

  l=50;
  i=0;
  v=n;
  o=n;

  while (i<l) {
      o = o+o;
      o = o+v;
      i = i+1;
  }

  while (l<i) {
      o = o+v+v;
      l = l+1;
  }

}
