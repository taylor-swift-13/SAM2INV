int main1(int a,int n,int p,int q){
  int l, i, v, t, e;

  l=(n%6)+19;
  i=0;
  v=8;
  t=n;
  e=p;

  while (i<l) {
      v = v+1;
      e = e+4;
      t = t+i;
      i = i+1;
  }

}
