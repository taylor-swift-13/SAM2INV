int main1(int a,int n){
  int l, i, v, b;

  l=(n%39)+12;
  i=0;
  v=n;
  b=-3;

  while (i<l) {
      b = b+b;
      b = b+v;
      i = i+4;
  }

  while (l<v) {
      l = l*2;
  }

}
