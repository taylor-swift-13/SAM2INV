int main1(int a,int b,int k,int m){
  int l, i, v, y, o, s, q;

  l=(a%37)+5;
  i=1;
  v=m;
  y=1;
  o=a;
  s=a;
  q=b;

  while (i<l) {
      v = v+1;
      y = y+1;
      o = o+1;
      s = v+y+o;
      v = v+y;
  }

}
