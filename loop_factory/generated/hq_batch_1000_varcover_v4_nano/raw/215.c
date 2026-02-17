int main1(int a,int p,int q){
  int l, i, v, t, b, d;

  l=45;
  i=0;
  v=a;
  t=-6;
  b=i;
  d=a;

  while (i<l) {
      d = v+t+b;
      v = v+1;
      d = t-d;
      i = i+1;
  }

}
