int main1(int a,int n){
  int l, i, v;

  l=n-2;
  i=0;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant l == n - 2;
    loop invariant i >= 0;
    loop invariant v >= a;
    loop invariant n == \at(n, Pre);
    loop invariant (l >= 0) ==> (0 <= i && i <= l);
    loop invariant (i == 0) ==> (v == a);
    loop invariant (i > 0) ==> (v >= 0);
    loop invariant 0 <= i;

    loop invariant l == \at(n, Pre) - 2;
    loop invariant l == \at(n,Pre) - 2;
    loop invariant (v >= 0) || (i == 0);
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v*v+v;
      v = v+v;
      i = i+1;
  }

}