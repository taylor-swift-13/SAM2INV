int main1(int k,int n){
  int l, i, v, f;

  l=45;
  i=l;
  v=-5;
  f=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant f == 45;
    loop invariant 0 <= i <= 45;
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant l == 45;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v >= -5;
    loop invariant i <= 45;
    loop invariant (v + 5) % 45 == 0;
    loop assigns v, i;
    loop variant i;
  */
  while (i>0) {
      v = v+f;
      i = i/2;
  }

}