int main1(int a,int k,int p,int q){
  int l, i, v, g, o, c;

  l=k;
  i=l;
  v=8;
  g=q;
  o=p;
  c=i;

  while (i>0) {
      v = v+2;
      g = g+v;
      o = o+g;
      v = v*2;
      g = g/2;
      if (c+4<l) {
          o = o*g;
      }
  }

}
