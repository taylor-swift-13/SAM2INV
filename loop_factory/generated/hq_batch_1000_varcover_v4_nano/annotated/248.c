int main1(int b,int n,int p){
  int l, i, v, q, t, m, x, d, u, f;

  l=46;
  i=0;
  v=b;
  q=i;
  t=n;
  m=i;
  x=-1;
  d=n;
  u=l;
  f=l;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant v == b + i*(i-1)/2;

    loop invariant q == 0;

    loop invariant t == n;

    loop assigns v, q, t, i;

    loop variant l - i;

  */
  while (i < l) {
      v = v + i;
      q = q * q;
      t = t + v * q;
      i = i + 1;
  }

}