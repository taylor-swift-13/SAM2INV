int main1(int b,int n,int p){
  int l, i, v, u, z, j, q, x, h;

  l=b+7;
  i=0;
  v=0;
  u=2;
  z=l;
  j=p;
  q=n;
  x=n;
  h=p;

  
  /*@

    loop invariant i >= 0;

    loop invariant v == 0;

    loop invariant u == 2;

    loop invariant l == \at(b, Pre) + 7;

    loop invariant b == \at(b, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop invariant i <= l || l <= 0;

    loop assigns i, v, u;

    loop variant l - i;

  */
while (i<l) {
      v = v*2;
      u = u+v;
      i = i+1;
  }

}