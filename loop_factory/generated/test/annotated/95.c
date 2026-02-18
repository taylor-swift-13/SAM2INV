int main1(int a,int b,int n,int p){
  int l, i, v;

  l=n+15;
  i=0;
  v=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == n + 15;
    loop invariant i % 4 == 0;

    loop invariant v >= i;
    loop invariant v % 2 == 0;
    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && n == \at(n, Pre) && p == \at(p, Pre);
    loop invariant l == \at(n, Pre) + 15;
    loop invariant i >= 0;
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant v >= 6;
    loop invariant b == \at(b, Pre);
    loop invariant p == \at(p, Pre);

    loop invariant v >= i + 6;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+v;
      v = v+i;
      i = i+4;
  }

}