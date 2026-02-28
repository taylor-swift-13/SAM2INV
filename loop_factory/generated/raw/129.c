int main129(int a,int m,int n){
  int c, o, b, v, d;

  c=a-7;
  o=c;
  b=m;
  v=n;
  d=m;

  while (o-1>=0) {
      v = v+b;
  }

  while (o-1>=0) {
      d = d+1;
      v = v-1;
      d = d+o;
      v = v*v;
  }

  while (v+2<=o) {
      b = b+3;
      b = b+v;
      d = d*d;
  }

}
