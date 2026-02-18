int main1(int a,int n,int p,int q){
  int l, i, v, t, e;

  l=(n%6)+19;
  i=0;
  v=8;
  t=n;
  e=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant t == n + i*(i-1)/2;
    loop invariant e == p + 4*i;
    loop invariant v == 8 + i;
    loop invariant i <= l;
    loop invariant a == \at(a, Pre) && n == \at(n, Pre) && p == \at(p, Pre) && q == \at(q, Pre);
    loop invariant i >= 0;
    loop invariant t == n + i*(i - 1)/2;
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant 0 <= i <= l;
    loop invariant l == ((\at(n,Pre)) % 6) + 19;
    loop invariant a == \at(a,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant p == \at(p,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant t == \at(n, Pre) + i*(i-1)/2;
    loop invariant e == \at(p, Pre) + 4*i;
    loop invariant l == (\at(n, Pre) % 6) + 19;
    loop assigns v, e, t, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      e = e+4;
      t = t+i;
      i = i+1;
  }

}