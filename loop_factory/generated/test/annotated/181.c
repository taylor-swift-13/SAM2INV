int main1(int k,int n,int p,int q){
  int l, i, v, s;

  l=k;
  i=l;
  v=n;
  s=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == \at(n, Pre) + 2 * s * (\at(k, Pre) - i);

    loop invariant i <= \at(k, Pre);
    loop invariant l == k;
    loop invariant s == \at(p, Pre);
    loop invariant v == \at(n, Pre) + 2 * \at(p, Pre) * (\at(k, Pre) - i);
    loop invariant v == n + 2*s*(k - i);
    loop invariant i <= k;
    loop invariant s == p;
    loop invariant k - i >= 0;
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant v == n + 2 * p * (k - i);
    loop assigns v, i;
  */
  while (i>0) {
      v = v+s+s;
      i = i-1;
  }

}