int main1(int b,int k,int m,int n){
  int l, i, v;

  l=m-2;
  i=0;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == m + i*(i+1)/2;
    loop invariant 0 <= i;
    loop invariant l == m - 2;
    loop invariant (l >= 0) ==> (0 <= i && i <= l);
    loop invariant v == m + (i * (i + 1)) / 2;

    loop invariant b == \at(b, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant m == \at(m, Pre);
    loop assigns i, v;
  */
  while (i<l) {
      v = v+1;
      v = v+i;
      i = i+1;
  }

}