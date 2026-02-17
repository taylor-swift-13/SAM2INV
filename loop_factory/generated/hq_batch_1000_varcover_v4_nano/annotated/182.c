int main1(int a,int m,int p){
  int l, i, v, u, x, y, e, t, o;

  l=67;
  i=0;
  v=i;
  u=i;
  x=i;
  y=-4;
  e=m;
  t=m;
  o=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant 0 <= i;
    loop invariant l == 67;
    loop invariant v == 0;
    loop invariant u == 0;
    loop assigns v, u, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v*2;
      u = u+v;
      i = i+1;
  }

}