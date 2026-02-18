int main1(int k,int m,int n,int p){
  int l, i, v, d, j;

  l=24;
  i=l;
  v=i;
  d=i;
  j=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == l + l*(l - i) - ((l - i)*(l - i - 1))/2;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v >= l;
    loop invariant i <= 24;
    loop invariant l == 24;
    loop invariant v == 24 + (24 - i) * (25 + i) / 2;
    loop invariant v == 24 + (24 - i) * 24 - ((24 - i) * (23 - i)) / 2;
    loop invariant v >= 24;
    loop invariant v <= 324;
    loop invariant v >= i;
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v+i;
      i = i-1;
  }

}