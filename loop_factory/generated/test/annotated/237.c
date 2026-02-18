int main1(int a,int n){
  int l, i, v, z;

  l=(n%8)+18;
  i=0;
  v=2;
  z=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant l == (n % 8) + 18;
    loop invariant 0 <= i <= l;
    loop invariant v >= 2;
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant l == (\at(n, Pre) % 8) + 18;
    loop invariant a == \at(a,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant l == (\at(n,Pre) % 8) + 18;
    loop invariant (v + 1) % 3 == 0;
    loop invariant v >= 2*i + 2;
    loop invariant 0 <= i;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v*2+1;
      i = i+1;
  }

}