int main1(int a,int b,int k,int n){
  int l, i, v, f, t;

  l=42;
  i=0;
  v=1;
  f=k;
  t=a;

  while (i<l) {
      v = v*v+v;
      v = v%6;
      if (v+2<l) {
          v = v%6;
      }
      i = i+1;
  }

}
