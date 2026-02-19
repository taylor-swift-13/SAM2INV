int main1(int k,int n){
  int l, i, v, m;

  l=(k%33)+7;
  i=0;
  v=-8;
  m=8;

  while (i<l) {
      v = v+3;
      m = m+v;
      i = i+1;
  }

  while (l>0) {
      m = m+m;
      m = m+i;
      l = l-1;
  }

}
