int main1(int a,int n){
  int l, i, v;

  l=58;
  i=0;
  v=n;

  while (i<l) {
      v = v+i;
      i = i+1;
  }

  while (l<i) {
      v = v+l;
      l = l+2;
  }

}
