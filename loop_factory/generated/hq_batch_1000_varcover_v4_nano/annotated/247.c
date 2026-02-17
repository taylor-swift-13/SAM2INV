int main1(int n,int p,int q){
  int l, i, v, m, d, f;

  l=38;
  i=0;
  v=q;
  m=l;
  d=-2;
  f=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == q + 3*i;
    loop invariant d == -2 + 3*i;
    loop invariant m == 38 - 4*i + (3*i*(i-1))/2;
    loop invariant l == 38;
    loop invariant q == \at(q, Pre);
    loop assigns v, d, m, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+3;
      d = d+2;
      m = m+f;
      m = m+d;
      d = d+1;
      i = i+1;
  }

}