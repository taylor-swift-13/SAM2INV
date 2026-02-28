int main1(int a,int m,int n,int p){
  int s, h, v, b, j, e;

  s=21;
  h=s;
  v=a;
  b=-6;
  j=-6;
  e=3;

  while (h>=1) {
      e = e*e+v;
      v = v%6;
      e = b*b;
      v = b*b;
      h = h-1;
  }

}
