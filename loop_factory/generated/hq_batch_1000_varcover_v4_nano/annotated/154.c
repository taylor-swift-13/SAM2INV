int main1(int a,int b,int n){
  int l, i, v, f, r, q, g, t, k;

  l=15;
  i=l;
  v=b;
  f=l;
  r=i;
  q=l;
  g=-4;
  t=-8;
  k=i;

  
  /*@

    loop invariant f == l;

    loop invariant (v - b) % l == 0;

    loop invariant v >= b;

    loop invariant i >= 0;

    loop invariant i <= l;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+f;
      i = i/2;
  }

}