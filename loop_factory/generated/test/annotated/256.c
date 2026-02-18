int main1(int a,int q){
  int l, i, v, z;

  l=q+16;
  i=0;
  v=i;
  z=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i;
    loop invariant v == i*(i - 1)/2;
    loop invariant l == q + 16;
    loop invariant (i == 0) ==> (z == q);
    loop invariant (i > 0) ==> (z >= 0);
    loop invariant a == \at(a, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant (l < 0) || (0 <= i && i <= l);
    loop invariant v == i*(i-1)/2;

    loop invariant v == i*(i - 1) / 2;
    loop invariant i >= 0;

    loop assigns v, z, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+i;
      z = z*z;
      i = i+1;
  }

}