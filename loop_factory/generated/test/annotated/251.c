int main1(int m,int p){
  int l, i, v;

  l=m+16;
  i=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == m + 16;
    loop invariant i >= 0;
    loop invariant p == \at(p, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant i <= l || l < 0;
    loop invariant v >= p;
    loop invariant (i <= l) || (l < 0);
    loop invariant (i == 0) ==> (v == p);
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      if (v*v<=l+4) {
          v = v*v+v;
      }
      if (v+6<l) {
          v = v*v;
      }
      i = i+1;
  }

}