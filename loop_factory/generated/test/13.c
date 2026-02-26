int main13(int a,int m,int q){
  int c, r, l, v;

  c=q+19;
  r=c;
  l=r;
  v=a;

  while (r>0) {
      if (r<c/2) {
          l = l+v;
      }
      else {
          l = l*v;
      }
      l = l+r;
      v = v*v;
      v = v+l*v;
  }

}
