int main1(int a,int b,int m){
  int l, i, v, p, o, q, f, u, g, c;

  l=m;
  i=0;
  v=-6;
  p=3;
  o=l;
  q=b;
  f=a;
  u=5;
  g=-5;
  c=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i;
    loop invariant (i <= l) || (l < 0);
    loop invariant v == -6 + i*(i-1)/2;
    loop invariant l == m;
    loop assigns v, i;
  */
  while (i<l) {
      v = v+i;
      i = i+1;
  }

}