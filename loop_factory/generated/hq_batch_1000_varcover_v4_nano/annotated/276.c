int main1(int a,int m,int p,int q){
  int l, i, v, n, x, h, g;

  l=14;
  i=l;
  v=a;
  n=-2;
  x=a;
  h=q;
  g=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant n == 2*v - 2*a - 2;
    loop invariant a == \at(a, Pre);
    loop assigns v, n, i;
    loop variant i;
  */
  while (i>0) {
      v = v*2;
      n = n+v;
      i = i-1;
  }

}