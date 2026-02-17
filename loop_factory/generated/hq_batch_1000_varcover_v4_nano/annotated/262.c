int main1(int k,int m,int n,int q){
  int l, i, v, r, f, b, s, d;

  l=52;
  i=0;
  v=k;
  r=k;
  f=-6;
  b=n;
  s=8;
  d=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant l == 52;
    loop invariant (k >= 0) ==> (r <= k);
    loop invariant (k >= 0) ==> (v >= k);
    loop assigns i, v, r;
    loop variant l - i;
  */
  while (i<l) {
      v = v*2;
      r = r/2;
      i = i+1;
  }

}