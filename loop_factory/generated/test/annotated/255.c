int main1(int k,int m){
  int l, i, v;

  l=(k%14)+7;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == (k % 14) + 7;

    loop invariant i >= 0;
    loop invariant v >= l;
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant l == (\at(k, Pre) % 14) + 7;
    loop invariant 0 <= i;
    loop invariant i <= l || l <= 0;
    loop invariant l <= 0 || v >= l;
    loop invariant l == ((\at(k,Pre) % 14) + 7);
    loop invariant k == \at(k,Pre);
    loop invariant m == \at(m,Pre);

    loop invariant (i == 0) ==> v == l;
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      if (i+1<=v+l) {
          v = v*v+v;
      }
      v = v*v+v;
      i = i+1;
  }

}