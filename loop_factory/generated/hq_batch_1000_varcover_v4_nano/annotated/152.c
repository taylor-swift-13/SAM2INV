int main1(int a,int p,int q){
  int l, i, v, j, g, b, e, d, h, t;

  l=40;
  i=l;
  v=i;
  j=-5;
  g=l;
  b=l;
  e=p;
  d=q;
  h=l;
  t=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant j == -5;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == 5*i - 4*l;
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v+j;
      i = i-1;
  }

}