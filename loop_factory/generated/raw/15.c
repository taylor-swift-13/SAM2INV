int main15(int a,int m,int p){
  int l, i, v, c, s;

  l=a+11;
  i=l+2;
  v=6;
  c=a;
  s=m;

  while (i>l) {
      v = v+4;
      c = c+v;
      s = s+c;
      v = v*v+v;
      v = v%7;
  }

  while (1) {
      i = i+2;
      c = c+i;
      v = v+1;
  }

}
