int main32(int m,int n,int p){
  int l, r, v, u, w;

  l=49;
  r=l;
  v=6;
  u=0;
  w=m;

  while (v<l) {
      if (v<l) {
          v = v+1;
      }
  }

  while (1) {
      if (l>=w) {
          break;
      }
      if (u<=v) {
          v = u;
      }
      l = l+1;
  }


  /*@ assert (l>=w); */
}
