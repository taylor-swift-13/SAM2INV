int main1(int a,int b,int n,int p){
  int l, i, v, e, f, x, k;

  l=(a%16)+18;
  i=l;
  v=3;
  e=l;
  f=p;
  x=a;
  k=i;

  while (i>0) {
      x = x*x+v;
      v = v%4;
      i = i/2;
  }

}
