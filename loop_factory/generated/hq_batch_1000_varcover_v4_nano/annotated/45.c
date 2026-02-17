int main1(int a,int b,int q){
  int l, i, v, x, y, j, w, s;

  l=56;
  i=l;
  v=i;
  x=4;
  y=a;
  j=-3;
  w=q;
  s=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant v >= i;
    loop invariant v >= l;
    loop invariant v % 4 == 0;
    loop assigns i, v;
  */
  while (i>0) {
      v = v*4;
      i = i-1;
  }

}