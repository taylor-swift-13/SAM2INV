int main1(int b,int n){
  int l, i, v;

  l=46;
  i=l;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= 46;
    loop invariant v % 2 == 0;
    loop invariant l == 46;
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant (0 <= i) && (i <= 46);
    loop invariant (v == 0) || (v == 2) || (v == 4) || (v == 8);
    loop invariant 0 <= i <= l;
    loop invariant v >= 0;
    loop invariant 0 <= i <= 46;
    loop assigns i, v;
  */
  while (i>0) {
      if (i+7<=v+l) {
          v = v%8;
      }
      else {
          v = v*2;
      }
      i = i-1;
  }

}