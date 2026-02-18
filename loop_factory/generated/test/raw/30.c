int main1(int a,int k,int n,int p){
  int l, i, v, x, q;

  l=(k%38)+20;
  i=0;
  v=k;
  x=p;
  q=l;

  while (i<l) {
      x = x+q;
      q = q+v;
      v = v+q;
      i = i+1;
  }

}
