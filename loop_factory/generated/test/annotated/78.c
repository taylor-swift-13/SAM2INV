int main1(int a,int b,int k,int n){
  int l, i, v, m, r;

  l=47;
  i=l;
  v=i;
  m=a;
  r=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant i >= 0;
    loop invariant i <= 47;
    loop invariant v == 94 - i;
    loop invariant m == a + (47 - i) * 47 + ((47 - i) * (48 - i)) / 2;
    loop invariant i + v == 94;
    loop invariant m == a + (v - 47)*(v + 48)/2;
    loop invariant v >= 47;
    loop invariant m == a + 47*(47 - i) + ((47 - i) * (48 - i)) / 2;
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant m == a + (47 - i) * 47 + (47 - i) * (48 - i) / 2;
    loop invariant m == a + v*(v+1)/2 - 1128;
    loop assigns v, m, i;
    loop variant i;
  */
  while (i>0) {
      v = v+1;
      m = m+v;
      i = i-1;
  }

}