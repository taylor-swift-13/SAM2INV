int main1(int a,int b,int k,int n){
  int l, i, v, w, u, q, o;

  l=80;
  i=1;
  v=b;
  w=-8;
  u=k;
  q=a;
  o=1;

  while (i<l) {
      v = v*2;
      w = w+v;
      u = u%6;
      w = w*w+v;
      if (i+3<=i+l) {
          q = q*v;
      }
      i = i*2;
  }

}
