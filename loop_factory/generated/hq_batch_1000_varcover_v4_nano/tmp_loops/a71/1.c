int main1(int b,int k,int n,int p){
  int l, i, v, y, z, j, g, h;

  l=p+20;
  i=1;
  v=3;
  y=6;
  z=-1;
  j=-4;
  g=i;
  h=n;

  while (i<l) {
      j = j*j+v;
      v = v%6;
      if (h+7<l) {
          j = j*j+h;
      }
      z = z+y;
      i = i*3;
  }

}
