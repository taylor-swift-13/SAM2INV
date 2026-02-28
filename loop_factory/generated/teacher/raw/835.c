int main1(int k,int n,int q){
  int c, o, v, u, p, h;

  c=(q%33)+13;
  o=0;
  v=o;
  u=n;
  p=k;
  h=q;

  while (1) {
      v = v+1;
      u = u-1;
      p = p+o;
      if (u+6<c) {
          p = p+h;
      }
      o = o+1;
  }

}
