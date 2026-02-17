int main1(int a,int k,int n){
  int l, i, v, q, m;

  l=9;
  i=l;
  v=n;
  q=2;
  m=6;

  while (i>0) {
      v = v+1;
      q = q+v;
      q = q+i;
      if (i+6<=l+l) {
          v = v+1;
      }
      else {
          m = m+1;
      }
      i = i-1;
  }

}
