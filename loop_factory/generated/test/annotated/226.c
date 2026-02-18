int main1(int b,int n){
  int l, i, v;

  l=74;
  i=1;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 74;
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant i >= 1;
    loop invariant v >= 2;

    loop invariant i > 0;
    loop invariant v > 0;
    loop invariant v % 2 == 0;
    loop invariant v >= i;
    loop assigns i, v;
  */
  while (i<l) {
      v = v*v;
      v = v*2;
      i = i*2;
  }

}