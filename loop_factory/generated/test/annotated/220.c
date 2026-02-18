int main1(int k,int m){
  int l, i, v, e, d;

  l=11;
  i=0;
  v=m;
  e=l;
  d=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 11;
    loop invariant i == 0;
    loop invariant m == \at(m, Pre);
    loop invariant i <= l;
    loop invariant i >= 0;

    loop invariant (v == l) || (((v - m) % 2) == 0);
    loop invariant k == \at(k, Pre);
    loop invariant (v <= l) || (v <= m);
    loop invariant (v <= l) || (v == m);
    loop invariant 0 <= i && i <= l;
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