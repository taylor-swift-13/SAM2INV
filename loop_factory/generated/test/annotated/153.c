int main1(int a,int b,int n,int q){
  int l, i, v, w;

  l=16;
  i=0;
  v=n;
  w=l;

  
  /*@

    loop invariant l == 16;

    loop invariant 0 <= i && i <= l && i % 4 == 0;

    loop invariant 16 <= w && w <= l;

    loop invariant v >= \at(n, Pre) + 33*(i/4);

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && n == \at(n, Pre) && q == \at(q, Pre);

    loop invariant w == l;

    loop invariant i % 4 == 0;

    loop invariant v == n + 33 * (i / 4);

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i <= l;

    loop invariant w == 16;

    loop invariant v >= n;

    loop invariant v == n + (i/4) * (2*w + 1);

    loop invariant v == n + (i/4) * (2*l + 1);

    loop assigns i, v, w;

    loop variant l - i;

  */
while (i<l) {
      v = v+w+w;
      v = v+1;
      if (w+6<l) {
          w = w+1;
      }
      i = i+4;
  }

}