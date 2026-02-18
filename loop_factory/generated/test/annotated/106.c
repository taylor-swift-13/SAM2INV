int main1(int k,int m,int n,int q){
  int l, i, v, z;

  l=43;
  i=0;
  v=l;
  z=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 43;
    loop invariant z == 0;
    loop invariant v == l + i;
    loop invariant i <= l;
    loop invariant (k == \at(k, Pre)) && (m == \at(m, Pre)) && (n == \at(n, Pre)) && (q == \at(q, Pre));
    loop invariant 0 <= i && i <= l;
    loop invariant v == 43 + i;
    loop invariant k == \at(k,Pre);
    loop invariant m == \at(m,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i >= 0;
    loop invariant v == 43 + i*(2*z + 1);
    loop invariant k == \at(k,Pre) && m == \at(m,Pre) && n == \at(n,Pre) && q == \at(q,Pre);
    loop invariant k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && q == \at(q, Pre);
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+z+z;
      v = v+1;
      i = i+1;
  }

}