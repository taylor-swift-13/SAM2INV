int main1(int a,int n){
  int l, i, v;

  l=41;
  i=0;
  v=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i % 5 == 0;
    loop invariant l == 41;

    loop invariant (v == -2) || (v > 0);
    loop invariant (i % 5) == 0;
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant i <= l + 4;
    loop invariant i >= 0;
    loop invariant v >= -2;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      if ((i%5)==0) {
          v = v*v;
      }
      else {
          v = v*v+v;
      }
      i = i+5;
  }

}