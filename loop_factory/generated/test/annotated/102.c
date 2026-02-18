int main1(int b,int m,int p,int q){
  int l, i, v, u;

  l=56;
  i=0;
  v=1;
  u=q;

  
  /*@

    loop invariant l == 56;

    loop invariant i % 4 == 0;

    loop invariant i <= l;

    loop invariant v == 1 + (i / 4) * (2 * u + 1);

    loop invariant u == q;

    loop invariant p == \at(p, Pre);

    loop invariant 0 <= i <= l;

    loop invariant v == 1 + (i/4) * (2*u + 1);

    loop invariant q == \at(q, Pre);

    loop invariant 4*(v - 1) == i*(2*u + 1);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop assigns i, v;

  */
  while (i<l) {
      v = v+u+u;
      v = v+1;
      i = i+4;
  }

}