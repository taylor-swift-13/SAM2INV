int main1(int k,int m,int p,int q){
  int l, i, v, s, d, x, g, c;

  l=q+15;
  i=0;
  v=p;
  s=-6;
  d=l;
  x=k;
  g=i;
  c=5;

  while (v!=0&&s!=0) {
      if (v>s) {
          v = v-s;
      }
      else {
          s = s-v;
      }
      x = x*x+v;
      v = v%7;
      v = v*x;
      d = d%6;
      g = g*s;
  }

}
