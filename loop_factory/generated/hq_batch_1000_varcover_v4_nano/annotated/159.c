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

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant w == -6;

    loop invariant h == l;

    loop invariant (i == 0) ==> (v == -2);

    loop invariant (i > 0) ==> (g == h + i - 1);

    loop assigns v, g, w, i;

  */
  while (i<l) {
      v = v+g;
      g = g+w;
      w = w+3;
      g = h+i;
      w = w*2;
      i = i+1;
  }

}