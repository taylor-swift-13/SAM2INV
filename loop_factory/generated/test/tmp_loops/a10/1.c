int main1(int m,int n){
  int l, i, v, q;

  l=m+12;
  i=0;
  v=m;
  q=i;

  while (i<l) {
      q = q+q;
      q = q+v;
      i = i+1;
  }

  while (l>0) {
      q = q+1;
      i = i-1;
      l = l-1;
  }

}
