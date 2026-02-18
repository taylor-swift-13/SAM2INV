int main1(int a,int b,int k,int n){
  int l, i, v, f, c;

  l=(k%7)+12;
  i=0;
  v=5;
  f=i;
  c=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant l == (\at(k, Pre) % 7) + 12;
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant 0 <= i <= l;
    loop invariant 0 <= i && i <= l;
    loop invariant l == (k % 7) + 12;
    loop invariant v % 5 == 0;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v*2;
      i = i+1;
  }

}