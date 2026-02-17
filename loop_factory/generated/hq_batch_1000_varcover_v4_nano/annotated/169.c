int main1(int k,int p,int q){
  int l, i, v, f, h, m, r;

  l=76;
  i=0;
  v=i;
  f=4;
  h=k;
  m=l;
  r=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i == 0;
    loop invariant l == 76;
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant 0 <= v;
    loop invariant v <= l;
    loop invariant (v == l) || (v % 2 == 0);
    loop invariant k == \at(k, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns v;
  */
  while (i<l) {
      if (v+2<=l) {
          v = v+2;
      }
      else {
          v = l;
      }
  }

}