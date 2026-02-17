int main1(int a,int b,int k,int q){
  int l, i, v, t, m, g;

  l=(q%33)+10;
  i=l;
  v=i;
  t=l;
  m=4;
  g=q;

  while (i>0) {
      v = v+1;
      t = t+1;
      v = v+t;
      t = t+m;
  }

}
