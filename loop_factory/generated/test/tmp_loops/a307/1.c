int main1(int k,int n){
  int l, i, v, q;

  l=k-1;
  i=l;
  v=i;
  q=i;

  while (i>0) {
      v = v*3;
      q = q/3;
      v = v+q+q;
  }

  while (q<i) {
      l = l+l;
      l = l+v;
      q = q+1;
  }

}
