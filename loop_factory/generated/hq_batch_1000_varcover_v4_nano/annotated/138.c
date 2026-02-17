int main1(int k,int m,int n){
  int l, i, v, g, y, s, w, x, r, t;

  l=58;
  i=l;
  v=l;
  g=l;
  y=m;
  s=-1;
  w=n;
  x=n;
  r=n;
  t=-3;

  
  /*@

    loop invariant g == l;

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v >= l;

    loop invariant (v - l) % g == 0;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+g;
      i = i/2;
  }

}