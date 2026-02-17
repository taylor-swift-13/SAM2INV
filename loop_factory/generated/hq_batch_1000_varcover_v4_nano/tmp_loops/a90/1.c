int main1(int a,int b,int k,int m){
  int l, i, v, z, c, e, h, p;

  l=(a%27)+6;
  i=l;
  v=4;
  z=l;
  c=l;
  e=m;
  h=-2;
  p=l;

  while (i>0) {
      v = v+2;
      z = z+v;
      c = c+z;
      v = v+z;
      z = z+c;
      c = c+6;
      h = h*2;
      z = v*v;
  }

}
