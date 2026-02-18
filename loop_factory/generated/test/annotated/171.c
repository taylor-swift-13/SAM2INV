int main1(int a,int k,int m,int n){
  int l, i, v;

  l=(m%14)+14;
  i=l;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a,Pre);
    loop invariant k == \at(k,Pre);
    loop invariant m == \at(m,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant l == (\at(m,Pre) % 14) + 14;
    loop invariant v == 4 || v == m - 4;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant i >= 0;
    loop invariant i <= l;

    loop invariant l == (m % 14) + 14;
    loop invariant n == \at(n, Pre);
    loop invariant 0 <= i <= l;
    loop invariant (v == 4) || (v == m - 4);
    loop assigns i, v;
    loop variant i;
  */
while (i>0) {
      v = v+2;
      v = m+(-4);
      i = i/2;
  }

}