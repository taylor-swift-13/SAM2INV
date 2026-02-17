int main1(int a,int b,int p){
  int l, i, v, f, u, r, m, g;

  l=b-6;
  i=0;
  v=b;
  f=p;
  u=b;
  r=i;
  m=b;
  g=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == b + i;
    loop invariant f == p - i;
    loop invariant u == b + i;
    loop invariant r == i*(i-1)/2;
    loop invariant 0 <= i;
    loop invariant i <= l || l < 0;
    loop assigns v, f, u, r, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      f = f-1;
      u = u+1;
      r = r+i;
      i = i+1;
  }

}