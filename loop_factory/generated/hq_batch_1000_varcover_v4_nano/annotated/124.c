int main1(int n,int p,int q){
  int l, i, v, c, u, m, r, z;

  l=10;
  i=l;
  v=q;
  c=l;
  u=6;
  m=q;
  r=8;
  z=n;

  
  /*@

    loop invariant c == l + 2*v - 2*q;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns c, i, v;

  */
  while (i>0) {
      v = v*2;
      c = c+v;
      i = i-1;
  }

}