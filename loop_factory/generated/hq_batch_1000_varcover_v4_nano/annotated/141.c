int main1(int m,int n,int p){
  int l, i, v, s, t, w, k, u, b, a;

  l=24;
  i=0;
  v=l;
  s=-4;
  t=l;
  w=p;
  k=l;
  u=0;
  b=m;
  a=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant s == -4 + (i/2) * l;
    loop invariant v == l - 4*(i/2) + l * ((i/2) * ((i/2) - 1)) / 2;
    loop invariant 0 <= i <= l;
    loop invariant i % 2 == 0;
    loop assigns i, v, s;
  */
  while (i<l) {
      v = v+s;
      s = s+t;
      i = i+2;
  }

}