int main1(int a,int n,int p,int q){
  int l, i, v, f, w;

  l=(p%15)+16;
  i=l;
  v=n;
  f=n;
  w=l;

  
  /*@

    loop invariant l == (p % 15) + 16;

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant f == n;

    loop invariant w == l;

    loop invariant v == n + (l - i) * (f + w);

    loop invariant v == \at(n,Pre) + (((\at(p,Pre) % 15) + 16) - i) * ( \at(n,Pre) + ((\at(p,Pre) % 15) + 16) );

    loop invariant f == \at(n,Pre);

    loop invariant w == ((\at(p,Pre) % 15) + 16);

    loop invariant l == ((\at(p,Pre) % 15) + 16);

    loop invariant 0 <= i <= ((\at(p,Pre) % 15) + 16);

    loop invariant v == n + (l - i) * (n + l);

    loop invariant a == \at(a, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant v + i*(f + w) == n + l*(n + l);

    loop invariant 0 <= i && i <= l;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+f+w;
      i = i-1;
  }

}