int main1(int k,int m,int p,int q){
  int l, i, v, c, z, w, b, o, g;

  l=q+10;
  i=1;
  v=-2;
  c=1;
  z=q;
  w=2;
  b=i;
  o=i;
  g=3;

  while (i<l) {
      v = v*2;
      c = c/2;
      if ((i%7)==0) {
          o = o*2;
      }
      if (k*k<=l+5) {
          c = c%4;
      }
      else {
          c = c*g;
      }
      w = w*b;
      w = w*2;
      i = i*2;
  }

}
