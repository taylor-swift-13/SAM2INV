int main1(int a,int b,int m,int n){
  int l, i, v;

  l=n;
  i=0;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant l == \at(n,Pre);
    loop invariant 0 <= i;

    loop invariant v >= l;
    loop invariant (i == 0) ==> (v == l);
    loop invariant l == n;
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant i == 0 ==> v == n;
    loop invariant a == \at(a, Pre) &&
                   b == \at(b, Pre) &&
                   m == \at(m, Pre) &&
                   n == \at(n, Pre);
    loop invariant (i <= l) || (l < 0);
    loop invariant m == \at(m, Pre);
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v*v;
      i = i+1;
  }

}