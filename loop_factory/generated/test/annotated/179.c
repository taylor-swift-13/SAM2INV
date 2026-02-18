int main1(int a,int k,int n,int p){
  int l, i, v;

  l=a+13;
  i=0;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == k + i + 4 * ((i + 4) / 5);
    loop invariant l == a + 13;
    loop invariant i >= 0;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);

    loop invariant 0 <= i && (l < 0 || i <= l);
    loop invariant v >= k;
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant 0 <= i;

    loop invariant k + i <= v;
    loop invariant v <= k + 5*i;
    loop assigns i, v;
    loop variant l - i;
  */
while (i<l) {
      if ((i%5)==0) {
          v = v+5;
      }
      else {
          v = v+1;
      }
      i = i+1;
  }

}