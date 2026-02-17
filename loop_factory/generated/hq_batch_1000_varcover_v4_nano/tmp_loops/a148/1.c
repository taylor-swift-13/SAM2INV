int main1(int b,int m,int n,int p){
  int l, i, v, d, r, e;

  l=60;
  i=1;
  v=b;
  d=m;
  r=b;
  e=5;

  while (i<l) {
      v = v+i;
      d = d*d;
      r = r+v*d;
      v = v*e;
      i = i*3;
  }

}
