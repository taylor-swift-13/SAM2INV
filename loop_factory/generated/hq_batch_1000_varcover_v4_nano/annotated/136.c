int main1(int a,int b,int n){
  int l, i, v, h, t, y, m, c, j, s;

  l=19;
  i=l;
  v=i;
  h=-8;
  t=-6;
  y=0;
  m=a;
  c=a;
  j=b;
  s=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 19;
    loop invariant v >= 0;
    loop invariant v <= 3*v + 5;
    loop assigns v;
  */
  while (v<l) {
      if (v<l) {
          v = v+1;
      }
      v = v*3+2;
  }

}