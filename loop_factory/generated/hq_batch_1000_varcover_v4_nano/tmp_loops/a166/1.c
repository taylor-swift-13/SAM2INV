int main1(int a,int b,int k,int q){
  int l, i, v, s, w, y, m, r;

  l=(b%13)+17;
  i=l;
  v=i;
  s=k;
  w=-1;
  y=-8;
  m=q;
  r=a;

  while (i>0) {
      y = y*y+v;
      v = v%9;
      if (v+5<l) {
          v = v*v+y;
      }
      else {
          v = v+r;
      }
      m = m*m+r;
      m = m+s;
      i = i-1;
  }

}
