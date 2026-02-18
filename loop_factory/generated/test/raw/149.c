int main1(int b,int m,int n,int p){
  int l, i, v, q, s;

  l=69;
  i=0;
  v=l;
  q=p;
  s=n;

  while (i<l) {
      q = q+s;
      s = s+v;
      v = v+i;
      s = l;
      q = q+1;
      q = q+s;
      i = i+1;
  }

}
