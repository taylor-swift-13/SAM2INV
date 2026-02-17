int main1(int a,int b,int k,int n){
  int l, i, v, z, y, q, u;

  l=66;
  i=0;
  v=5;
  z=a;
  y=l;
  q=i;
  u=8;

  while (i<l) {
      v = v*3;
      z = z/3;
      if ((i%5)==0) {
          q = q*y;
      }
      else {
          z = y+i;
      }
      v = y+i;
      v = v*v+q;
      q = q%6;
      i = i+2;
  }

}
