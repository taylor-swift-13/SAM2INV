int main1(int a,int k,int m,int n){
  int l, i, v;

  l=(m%14)+14;
  i=l;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre);
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == 0 || v == 4;
    loop invariant l == (\at(m,Pre) % 14) + 14;
    loop invariant a == \at(a,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant m == \at(m,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant 0 <= i;
    loop invariant i <= (\at(m,Pre) % 14) + 14;
    loop invariant v >= 0;
    loop invariant v <= 4;
    loop invariant l == (m % 14) + 14;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant l == (\at(m, Pre) % 14) + 14;
    loop assigns i, v;
    loop variant i;
  */
  while (i>0) {
      v = v%4;
      i = i/2;
  }

}