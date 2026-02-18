int main1(int b,int k,int p,int q){
  int l, i, v, x, n;

  l=77;
  i=l;
  v=-2;
  x=b;
  n=l;

  
  /*@

    loop invariant i >= 0;

    loop invariant i + x == b + 77;

    loop invariant v == -2 + (77 - i) * (b + 78) + ((77 - i) * (76 - i)) / 2;

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant x == b + (l - i);

    loop invariant v == -2 + (l - i) * (b + n + 1) + ((l - i) * (l - i - 1)) / 2;

    loop invariant n == l;

    loop invariant i <= l;

    loop invariant l == 77;

    loop invariant n == 77;

    loop invariant x == b + 77 - i;

    loop invariant 0 <= i <= 77;

    loop invariant x >= b;

    loop invariant 0 <= i <= l;

    loop invariant x + i == b + l;

    loop invariant b <= x <= b + l;

    loop invariant v == -2 + (l - i)*(b + n + 1) + ((l - i)*(l - i - 1))/2;

    loop assigns v, x, i;

    loop variant i;

  */
  while (i>0) {
      v = v+x+n;
      v = v+1;
      x = x+1;
      i = i-1;
  }

}