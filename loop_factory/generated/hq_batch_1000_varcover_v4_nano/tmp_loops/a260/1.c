int main1(int a,int m,int p,int q){
  int l, i, v, u, o, c, k, g;

  l=30;
  i=1;
  v=-3;
  u=p;
  o=a;
  c=-2;
  k=q;
  g=6;

  while (i<l) {
      v = v+i;
      u = u*u;
      o = o+v*u;
      if ((i%6)==0) {
          g = g+o;
      }
      else {
          v = v*k;
      }
      i = i*3;
  }

}
