int main1(int b,int k,int m,int n){
  int l, i, v;

  l=n-2;
  i=0;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@

    loop invariant (i == 0) ==> (v == 0);
    loop invariant (i > 0) ==> (v == i - 1);
    loop invariant l == n - 2;
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant i >= 0;
    loop invariant v >= 0;
    loop invariant v <= i;
    loop invariant l == \at(n, Pre) - 2;
    loop invariant b == \at(b, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre);
    loop invariant (i <= l) || (i == 0);
    loop invariant (b == \at(b, Pre)) && (k == \at(k, Pre)) && (m == \at(m, Pre)) && (n == \at(n, Pre));
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v-v;
      v = v+i;
      i = i+1;
  }

}