int main1(int b,int m,int q){
  int l, i, v, g, w, u, y, t, c, h;

  l=(b%8)+7;
  i=0;
  v=-2;
  g=b;
  w=-6;
  u=-3;
  y=2;
  t=l;
  c=q;
  h=l;

  while (i<l) {
      v = v+g;
      g = g+w;
      w = w+3;
      g = h+i;
      w = w*2;
      i = i+1;
  }

}
