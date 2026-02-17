int main1(int a,int b,int k,int p){
  int l, i, v, y, s, h, j, r, f, o;

  l=a+24;
  i=l;
  v=-5;
  y=l;
  s=a;
  h=i;
  j=k;
  r=a;
  f=l;
  o=i;

  while (i>0) {
      if (i<l/2) {
          v = v+y;
      }
      else {
          v = v*y;
      }
      v = v+i;
      y = y*y;
      s = s+v*y;
      r = r*2;
      s = s*s+y;
      j = s+i;
      s = s%7;
  }

}
