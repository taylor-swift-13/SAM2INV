int main1(int k,int n,int p,int q){
  int l, i, v, s, b, z, j, y, r;

  l=k-9;
  i=1;
  v=n;
  s=5;
  b=l;
  z=l;
  j=n;
  y=q;
  r=n;

  while (v!=0&&s!=0) {
      if (v>s) {
          v = v-s;
      }
      else {
          s = s-v;
      }
      z = z*z+v;
      v = v%4;
      j = r*r;
      y = y*s;
  }

}
