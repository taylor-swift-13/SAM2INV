int main1(int a,int n,int p,int q){
  int l, i, v, b;

  l=12;
  i=l;
  v=n;
  b=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i <= 12;
    loop invariant i >= 0;
    loop invariant l == 12;
    loop invariant b == -1;
    loop invariant v == n + (12 - i) * (2*b + 1);
    loop invariant v - i == n - 12;
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant v == n - 12 + i;
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v == n + i - 12;
    loop invariant v >= n - 12;
    loop invariant v <= n;
    loop invariant i <= l;
    loop invariant v == n + i - l;
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v+b+b;
      v = v+1;
      i = i-1;
  }

}