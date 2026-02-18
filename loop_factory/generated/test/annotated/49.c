int main1(int m,int n,int p,int q){
  int l, i, v, r;

  l=47;
  i=0;
  v=8;
  r=n;

  
  /*@

    loop invariant v == 8 + 2*i;

    loop invariant r == n + i*i + 9*i;

    loop invariant i <= l;

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant l == 47;

    loop invariant r == n + i*(i+9);

    loop invariant 0 <= i <= l;

    loop invariant r == \at(n, Pre) + i*i + 9*i;

    loop assigns i, v, r;

    loop variant l - i;

  */
  while (i<l) {
      v = v+2;
      r = r+v;
      i = i+1;
  }

}