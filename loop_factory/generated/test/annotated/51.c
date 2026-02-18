int main1(int a,int b,int k,int q){
  int l, i, v, w, n;

  l=k-2;
  i=0;
  v=q;
  w=k;
  n=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant l == k - 2;
    loop invariant w == k;
    loop invariant n == 8;
    loop invariant v == q + i*(k + n);
    loop invariant v == q + i*(k+8);
    loop invariant i <= l || l < 0;
    loop invariant v == q + i*(w + n);
    loop invariant k == \at(k, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant a == \at(a, Pre);
    loop invariant v == \at(q, Pre) + i*(w + n);

    loop assigns v, i;
  */
  while (i<l) {
      v = v+w+n;
      i = i+1;
  }

}