int main1(int a,int k,int n){
  int l, i, v, o, j, e, y, x;

  l=49;
  i=0;
  v=k;
  o=l;
  j=l;
  e=n;
  y=6;
  x=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant v == k + i;
    loop invariant e == n + i;
    loop invariant x == a + i*y;
    loop invariant j >= l + i;
    loop assigns v, j, e, x, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      j = j+1;
      e = e+1;
      x = x+y;
      if (i+5<=n+l) {
          j = j+i;
      }
      i = i+1;
  }

}