int main1(int k,int n,int q){
  int l, i, v, u, x, m, h;

  l=23;
  i=0;
  v=k;
  u=i;
  x=i;
  m=q;
  h=2;

  
  /*@

    loop invariant u == 2*v - 2*\at(k, Pre);

    loop invariant 0 <= i && i <= l;

    loop invariant x == 0;

    loop invariant k == \at(k, Pre) && n == \at(n, Pre) && q == \at(q, Pre);

    loop assigns v, u, x, i;

    loop variant l - i;

  */
while (i<l) {
      v = v*2;
      u = u+v;
      x = x%2;
      if (i+6<=x+l) {
          x = x*2;
      }
      i = i+1;
  }

}