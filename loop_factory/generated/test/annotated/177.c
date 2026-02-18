int main1(int a,int m,int n,int p){
  int l, i, v, f, j;

  l=(m%6)+16;
  i=0;
  v=6;
  f=n;
  j=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant v == 6 + i * (f + j);
    loop invariant l == (m % 6) + 16;
    loop invariant j == n;
    loop invariant n == \at(n, Pre);
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == 6 + i*(f + j);
    loop invariant l == (\at(m, Pre) % 6) + 16;
    loop invariant a == \at(a, Pre);
    loop invariant 0 <= i;
    loop invariant f == n;
    loop invariant m == \at(m, Pre);
    loop invariant v == 6 + (f + j) * i;
    loop assigns i, v;
  */
  while (i<l) {
      v = v+f+j;
      i = i+1;
  }

}