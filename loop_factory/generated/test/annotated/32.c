int main1(int b,int m,int n,int p){
  int l, i, v;

  l=m-10;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == m - 10;
    loop invariant (l < 0) || (i <= l);
    loop invariant i >= 0;

    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant 0 <= i;
    loop invariant v == l || v >= 0;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      if (i+3<=n+l) {
          v = v*v;
      }
      i = i+1;
  }

}