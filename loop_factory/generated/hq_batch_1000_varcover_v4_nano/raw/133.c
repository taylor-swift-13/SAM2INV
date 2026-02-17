int main1(int b,int n,int q){
  int l, i, v, o;

  l=(b%7)+14;
  i=0;
  v=n;
  o=n;

  while (i<l) {
      v = v+1;
      o = o-1;
      v = v+i;
      i = i+1;
  }

}
