int main1(int a,int b,int k,int n){
  int l, i, v, d, z, o, r, s;

  l=36;
  i=0;
  v=-2;
  d=4;
  z=a;
  o=k;
  r=1;
  s=6;

  while (i<l) {
      v = v*2;
      d = d+v;
      z = z%9;
      s = s*2;
      if ((i%5)==0) {
          s = s*r;
      }
      z = z%5;
      s = s*o;
      i = i+1;
  }

}
