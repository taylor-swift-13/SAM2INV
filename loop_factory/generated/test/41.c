int main41(int a,int b,int q){
  int e, x, v, y;

  e=(a%35)+8;
  x=1;
  v=3;
  y=x;

  while (x<e) {
      v = v*v+v;
      v = v%9;
      y = v*v;
      x = x*2;
  }

}
