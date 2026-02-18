int main1(int k,int m,int p,int q){
  int l, i, v, n;

  l=61;
  i=0;
  v=-2;
  n=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i % 3 == 0;
    loop invariant i >= 0;
    loop invariant n >= 3;
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i <= l + 2;
    loop invariant m == \at(m, Pre);

    loop invariant (i >= 3) ==> (n % 2 == 0);
    loop invariant l == 61;
    loop invariant v == -2;
    loop assigns i, n;
  */
  while (i<l) {
      n = n+n;
      n = n+v;
      i = i+3;
  }

}