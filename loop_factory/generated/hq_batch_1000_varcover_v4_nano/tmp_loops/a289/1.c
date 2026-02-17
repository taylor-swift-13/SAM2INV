int main1(int a,int b,int k,int m){
  int l, i, v, j, c, z, y, s, w;

  l=a;
  i=l;
  v=i;
  j=k;
  c=l;
  z=i;
  y=a;
  s=b;
  w=a;

  while (i>0) {
      if (i%6==2) {
          v = v+1;
      }
      else {
          j = j+1;
      }
      if (i%6==3) {
          c = c+1;
      }
      else {
      }
      z = z*z+v;
      v = v%8;
  }

}
