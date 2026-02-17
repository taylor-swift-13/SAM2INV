int main1(int n,int p,int q){
  int l, i, v, t, x, z, d, y, s, m;

  l=68;
  i=0;
  v=5;
  t=n;
  x=6;
  z=-4;
  d=0;
  y=p;
  s=q;
  m=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant t == n + i*i + 5*i;
    loop invariant x == 6 + 2*i;
    loop invariant v == 5 + i*n + i*(i-1)*(i+7)/3;
    loop assigns v, t, x, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+t;
      t = t+x;
      x = x+2;
      i = i+1;
  }

}