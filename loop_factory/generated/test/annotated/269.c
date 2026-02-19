int main1(int b,int n){
  int l, i, v;

  l=46;
  i=l;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 2;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant l == 46;
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant 0 <= i && i <= l;
    loop invariant 0 <= v && v <= 4;
    loop invariant v >= 0;
    loop invariant v <= 4;
    loop invariant 0 <= v <= 4;
    loop invariant 0 <= i;
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v%5;
      v = v%6;
      i = i-1;
  }

}