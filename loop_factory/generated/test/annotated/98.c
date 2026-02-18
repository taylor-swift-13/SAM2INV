int main1(int a,int m,int n,int q){
  int l, i, v;

  l=55;
  i=0;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 10*(v - \at(n, Pre)) == i*(i - 3);
    loop invariant i <= l;
    loop invariant i % 5 == 0;
    loop invariant i >= 0;
    loop invariant 0 <= i <= l;
    loop invariant v == n + (i*i - 3*i)/10;
    loop invariant n == \at(n, Pre) && a == \at(a, Pre) && m == \at(m, Pre) && q == \at(q, Pre);

    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant 0 <= i;
    loop invariant v - n == (i*i - 3*i) / 10;
    loop invariant v >= n;
    loop invariant l == 55;
    loop assigns v, i;
  */
  while (i<l) {
      v = v+i;
      v = v+1;
      i = i+5;
  }

}