int main1(int b,int m,int n,int p){
  int l, i, v, q, s;

  l=69;
  i=0;
  v=l;
  q=p;
  s=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant v == l + i*(i-1)/2;
    loop invariant (i == 0) ==> (q == p);
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant l == 69;
    loop invariant 0 <= i <= l;
    loop invariant (i == 0) ==> (s == n);
    loop invariant (i > 0) ==> (s == l);
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v == 69 + i*(i-1)/2;
    loop assigns q, s, v, i;
    loop variant l - i;
  */
while (i<l) {
      q = q+s;
      s = s+v;
      v = v+i;
      s = l;
      q = q+1;
      q = q+s;
      i = i+1;
  }

}