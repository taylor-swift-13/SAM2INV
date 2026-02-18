int main1(int a,int k,int m,int n){
  int l, i, v, p;

  l=29;
  i=l;
  v=n;
  p=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant v == n + 5 * (l - i);
    loop invariant p == a + (l - i) * n + 5 * (l - i) * (l - i + 1) / 2;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant l == 29;
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant v == n + 145 - 5*i;
    loop invariant p == a + (29 - i)*n + 5*(29 - i)*(30 - i)/2;
    loop invariant 0 <= i && i <= 29;
    loop invariant v == n + 5*(l - i);
    loop invariant p == a + (l - i) * (n + 5) + 5*(l - i)*(l - i - 1)/2;
    loop invariant 0 <= i && i <= l;
    loop invariant v == \at(n, Pre) + 5*(l - i);
    loop invariant p == \at(a, Pre) + (l - i)*\at(n, Pre) + 5*(l - i)*(l - i + 1)/2;
    loop invariant a == \at(a, Pre) && n == \at(n, Pre) && k == \at(k, Pre) && m == \at(m, Pre);
    loop assigns v, p, i;
    loop variant i;
  */
  while (i>0) {
      v = v+5;
      p = p+v;
      i = i-1;
  }

}