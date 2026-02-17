int main1(int a,int b,int m){
  int l, i, v, g, j, x;

  l=a;
  i=0;
  v=m;
  g=-2;
  j=l;
  x=5;

  while (i<l) {
      v = v*3+2;
      g = g*v+2;
      j = g*g;
      i = i+1;
  }

}
