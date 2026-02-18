int main1(int a,int b,int n,int q){
  int l, i, v, w;

  l=16;
  i=0;
  v=n;
  w=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant i <= l;
    loop invariant i % 4 == 0;
    loop invariant v == \at(n, Pre) + (i/4) * 33;
    loop invariant v == n + 33 * (i/4);
    loop invariant l == 16;
    loop invariant w == l;
    loop invariant q == \at(q, Pre);
    loop invariant 4*(v - \at(n, Pre)) == i*(2*w + 1);
    loop invariant i >= 0;
    loop invariant v >= \at(n, Pre);
    loop invariant v == n + (i/4) * (2*w + 1);
    loop invariant v == n + 33*(i/4);
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+w+w;
      v = v+1;
      i = i+4;
  }

}