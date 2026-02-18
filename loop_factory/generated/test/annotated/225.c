int main1(int n,int q){
  int l, i, v;

  l=q+8;
  i=0;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == q + 8;
    loop invariant q == \at(q, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant v % 2 == 0;
    loop invariant i >= 0;
    loop invariant i <= l || l < 0;

    loop invariant v >= 2;
    loop invariant 0 <= i;
    loop invariant l == \at(q, Pre) + 8;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      if (i+1<=q+l) {
          v = v*2;
      }
      i = i+1;
  }

}