int main1(int a,int k,int m,int p){
  int l, i, v, z, b, r;

  l=m;
  i=0;
  v=-8;
  z=l;
  b=4;
  r=l;

  while (i<l) {
      v = v*2+5;
      z = z*v+5;
      r = r*r+v;
      v = v%4;
      b = r*r;
      v = v%2;
      v = r*r;
  }

}
