int main1(int m,int q){
  int l, i, v, f;

  l=(m%15)+18;
  i=l;
  v=m;
  f=l;

  while (i>0) {
      i = i-1;
  }

  while (f>0) {
      v = v+3;
      l = l+v;
      f = f/2;
  }

}
