int main1(int a,int m,int n,int p){
  int l, i, v, d, z;

  l=(p%11)+10;
  i=0;
  v=a;
  d=a;
  z=m;

  /* >>> LOOP INVARIANTS TO FILL <<< */
    /*@
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v == a + 3*i;
    loop invariant z >= m + i;
    loop invariant z <= m + 4*i;
    loop invariant l == p % 11 + 10;
    loop invariant (i <= n + l - 1) ==> (z == m + 4*i);

    loop invariant 0 <= i <= l;

    loop invariant l == (p%11) + 10;
    loop invariant v == \at(a, Pre) + 3*i;
    loop invariant z - \at(m, Pre) - i >= 0;
    loop invariant (z - \at(m, Pre) - i) % 3 == 0;
    loop invariant z - \at(m, Pre) - i <= 3*i;
    loop invariant 0 <= i;
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant l == (\at(p,Pre) % 11) + 10;
    loop assigns i, v, z;
    loop variant l - i;
  */
while (i<l) {
      v = v+3;
      z = z+1;
      if (i+2<=n+l) {
          z = z+3;
      }
      i = i+1;
  }

}