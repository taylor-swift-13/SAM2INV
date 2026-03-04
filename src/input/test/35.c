int main35(int m,int p,int q){
  int r, s, v, b;

  r=q+7;
  s=r;
  v=q;
  b=8;

  while (s>3) {
      v = v*2+5;
      b = b*v+5;
      v = v+b;
      s = s-4;
  }

  while (1) {
      b = b+1;
      v = v+1;
      b = b+v+v;
  }

}
