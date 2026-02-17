int main1(int a,int m,int n,int p){
  int l, i, v, w, h, s, g, t;

  l=65;
  i=0;
  v=l;
  w=m;
  h=2;
  s=-5;
  g=i;
  t=m;

  while (i<l) {
      if (i<l/2) {
          v = v+w;
      }
      else {
          v = v*w;
      }
      v = v*2;
      w = w+v;
      h = h%4;
      v = v*h;
  }

}
