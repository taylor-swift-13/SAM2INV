int main1(int a,int k,int n,int p){
  int l, i, v, s, b;

  l=59;
  i=0;
  v=n;
  s=k;
  b=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant v == n + i;
    loop invariant s == k - i;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant i >= 0;
    loop invariant l == 59;
    loop invariant a == \at(a,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant v == i + \at(n,Pre);
    loop invariant s == \at(k,Pre) - i;
    loop invariant v == \at(n, Pre) + i;
    loop invariant s == \at(k, Pre) - i;
    loop assigns i, v, s;
  */
  while (i<l) {
      v = v+1;
      s = s-1;
      i = i+1;
  }

}