int main1(int b,int m,int p){
  int l, i, v, a, f, u, s, n;

  l=62;
  i=l;
  v=i;
  a=m;
  f=i;
  u=l;
  s=i;
  n=b;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant l == 62;

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop assigns i;

    loop variant i;

  */
while (i>0) {
      i = i/2;
  }

}