int main1(int b,int n,int q){
  int l, i, v, z, t;

  l=69;
  i=0;
  v=i;
  z=q;
  t=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i >= 0;
    loop invariant v >= 0;
    loop invariant 2*v == i;
    loop invariant i <= l + 1;
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+1;
      i = i+2;
  }

}