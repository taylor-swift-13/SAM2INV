int main25(int k,int m,int q){
  int l, u, c, v, w;

  l=64;
  u=0;
  c=k;
  v=k;
  w=q;

  while (c!=0&&v!=0) {
      if (c>v) {
          c = c-v;
      }
      else {
          v = v-c;
      }
      while (v>0) {
          u = u+1;
          l = l+1;
          u = u+l+l;
          u = u+1;
      }
      while (l<w) {
          u = u+2;
          u = u+l;
      }
  }


  /*@ assert l >= w; */
}
