int main1(int b,int m,int n,int q){
  int l, i, v, w, j;

  l=11;
  i=l;
  v=l;
  w=n;
  j=b;

  
  /*@

    loop invariant w == n + (l - i) * j;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i <= 11;

    loop invariant w == n + (11 - i) * j;

    loop invariant l == 11;

    loop invariant j == b;

    loop invariant w == n + (11 - i) * b;

    loop invariant 0 <= i <= l;

    loop invariant w == n + (l - i) * b;

    loop assigns w, i;

    loop variant i;

  */
  while (i>0) {
      w = w+j;
      i = i-1;
  }

}