int main1(int a,int b,int m,int q){
  int l, i, v, g, n;

  l=m-5;
  i=0;
  v=l;
  g=3;
  n=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && q == \at(q, Pre);
    loop invariant l == \at(m, Pre) - 5;
    loop invariant v == l + 3*i;
    loop invariant i >= 0;

    loop invariant l == m - 5;
    loop invariant v >= l;
    loop invariant 0 <= i;
    loop invariant i <= l || l < 0;

    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+3;
      i = i+1;
  }

}