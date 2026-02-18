int main1(int b,int k,int n,int q){
  int l, i, v, g, f;

  l=75;
  i=l;
  v=k;
  g=n;
  f=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i == 75;
    loop invariant l == 75;
    loop invariant (v <= k) || (v <= l);
    loop invariant i > 0;
    loop invariant v <= l || v == k;
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);

    loop invariant b == \at(b, Pre) && k == \at(k, Pre);
    loop invariant n == \at(n, Pre) && q == \at(q, Pre);

    loop invariant i <= 75;
    loop assigns v;
  */
  while (i>0) {
      if (v+6<=l) {
          v = v+6;
      }
      else {
          v = l;
      }
  }

}