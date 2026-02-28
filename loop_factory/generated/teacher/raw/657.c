int main1(int m,int q){
  int x, c, o, v, l, p;

  x=m+14;
  c=0;
  o=-3;
  v=x;
  l=c;
  p=6;

  while (c<x) {
      p = p*p+o;
      o = o%6;
      c = c+1;
  }

}
