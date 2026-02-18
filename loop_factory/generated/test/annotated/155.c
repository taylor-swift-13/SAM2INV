int main1(int a,int b,int m,int n){
  int l, i, v, g, x;

  l=30;
  i=l;
  v=l;
  g=6;
  x=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= 30;
    loop invariant v == 210 - 6*i;
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant 0 <= i && i <= l;
    loop invariant x % 2 == l % 2;

    loop invariant g == 6;
    loop invariant l == 30;
    loop invariant v + 6*i == 210;
    loop invariant i <= l;
    loop assigns v, x, i;
    loop variant i;
  */
  while (i>0) {
      v = v+3;
      x = x+2;
      if (i+5<=v+l) {
          x = g-x;
      }
      v = v+3;
      i = i-1;
  }

}