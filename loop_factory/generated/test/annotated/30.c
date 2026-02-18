int main1(int a,int k,int n,int p){
  int l, i, v, x, q;

  l=(k%38)+20;
  i=0;
  v=k;
  x=p;
  q=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;

    loop invariant l == (\at(k,Pre) % 38) + 20;
    loop invariant a == \at(a,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant p == \at(p,Pre);
    loop invariant l == ((\at(k, Pre) % 38) + 20);
    loop invariant k == \at(k, Pre);
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant v - q - x == k - l - p;
    loop invariant l == (k % 38) + 20;
    loop invariant (l < 0) || (i <= l);
    loop invariant 0 <= i;
    loop assigns i, x, q, v;
    loop variant l - i;
  */
  while (i<l) {
      x = x+q;
      q = q+v;
      v = v+q;
      i = i+1;
  }

}