int main74(int a,int b,int q){
  int p, f, v, l;

  p=q+24;
  f=p+2;
  v=f;
  l=a;

  while (1) {
      if (f>=p) {
          break;
      }
      v = v+2;
      f = f+1;
      v = v*3+3;
      l = l*v+3;
      l = l*2;
  }

}
