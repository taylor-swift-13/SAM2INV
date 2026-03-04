int main8(int b,int k,int p){
  int n, h, v, m;

  n=(b%8)+7;
  h=1;
  v=p;
  m=b;

  while (h*2<=n) {
      v = v*2;
      m = m+v;
      m = m%8;
      h = h*2;
  }

}
