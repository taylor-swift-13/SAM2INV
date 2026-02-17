int main1(int k,int p,int q){
  int l, i, v, r, t, d;

  l=k;
  i=0;
  v=q;
  r=i;
  t=-1;
  d=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l || l < 0;
    loop invariant v == q + i*(i-1)/2;
    loop invariant r == 0;
    loop invariant l == k;
    loop invariant q == \at(q, Pre);
    loop assigns v, r, i;
  */
  while (i<l) {
      v = v+i;
      r = r*r;
      i = i+1;
  }

}