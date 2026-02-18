int main1(int k,int m){
  int l, i, v;

  l=k+18;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == k + 18;
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant i >= 0;
    loop invariant v >= l;
    loop invariant 0 <= i;

    loop invariant l == \at(k, Pre) + 18;
    loop invariant (l <= 0) || (0 <= i && i <= l);
    loop invariant (l*l > l+5) ==> (v == l);

    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      if (l*l<=l+5) {
          v = v*v;
      }
      i = i+1;
  }

}