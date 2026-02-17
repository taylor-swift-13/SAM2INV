int main1(int m,int n,int p,int q){
  int l, i, v, h, z, g, j;

  l=(q%37)+8;
  i=1;
  v=-4;
  h=p;
  z=m;
  g=p;
  j=q;

  while (i<l) {
      v = v*3;
      h = h/3;
      h = h%2;
      g = g*g+v;
      i = i*3;
  }

}
