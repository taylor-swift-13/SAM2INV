int main1(int a,int p,int q){
  int l, i, v, r, h, b, y, n;

  l=30;
  i=l;
  v=-5;
  r=q;
  h=l;
  b=-1;
  y=a;
  n=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == -5 + 2*(l - i);

    loop invariant 0 <= i <= l;
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v+2;
      i = i-1;
  }

}