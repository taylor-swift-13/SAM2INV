int main1(int a,int b,int q){
  int l, i, v, e, t;

  l=(b%14)+17;
  i=0;
  v=q;
  e=i;
  t=q;

  while (i<l) {
      v = v+e+t;
      v = v+1;
      i = i+1;
  }

}
