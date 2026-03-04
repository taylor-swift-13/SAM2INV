int main69(int b,int k,int q){
  int f, l, v, o;

  f=(b%6)+14;
  l=0;
  v=5;
  o=l;

  while (1) {
      if (l>=f) {
          break;
      }
      v = v+2;
      l = l+1;
      v = v*v+v;
  }

}
