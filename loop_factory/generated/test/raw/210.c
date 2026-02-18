int main1(int a,int n,int p,int q){
  int l, i, v, f, w;

  l=(p%15)+16;
  i=l;
  v=n;
  f=n;
  w=l;

  while (i>0) {
      v = v+f+w;
      i = i-1;
  }

}
