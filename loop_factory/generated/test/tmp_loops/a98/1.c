int main1(int k,int n){
  int l, i, v, o;

  l=(k%17)+4;
  i=0;
  v=k;
  o=n;

  while (i<l) {
      i = i+4;
  }

  while (l<i) {
      v = v+1;
      o = o-1;
      o = o+o;
  }

}
