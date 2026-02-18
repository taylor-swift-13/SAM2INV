int main1(int k,int m,int n,int q){
  int l, i, v;

  l=26;
  i=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == \at(q,Pre) + i*(i-2)/4;
    loop invariant i % 2 == 0;
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant k == \at(k,Pre);
    loop invariant l == 26;
    loop invariant v == q + (i/2) * ((i/2) - 1);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i >= 0;
    loop invariant i >= 0 && i <= l;
    loop invariant v == \at(q, Pre) + (i/2) * ((i/2) - 1);
    loop assigns v, i;
  */
  while (i<l) {
      v = v+i;
      i = i+2;
  }

}