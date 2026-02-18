int main1(int b,int n){
  int l, i, v, w;

  l=54;
  i=l;
  v=i;
  w=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == 54;
    loop invariant i <= l;
    loop invariant i >= 0;
    loop invariant v % 54 == 0;
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant v >= l;
    loop invariant i <= 54;
    loop invariant v >= 54;
    loop invariant 0 <= i;
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v*2;
      i = i-1;
  }

}