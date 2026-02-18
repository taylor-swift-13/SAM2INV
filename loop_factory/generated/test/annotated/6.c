int main1(int b,int k,int m,int n){
  int l, i, v, q, s;

  l=(b%15)+18;
  i=0;
  v=3;
  q=n;
  s=m;

  
  /*@

    loop invariant 2*(q - \at(n, Pre)) == i * s;

    loop invariant 0 <= i && i <= l + 1;

    loop invariant i % 2 == 0;

    loop invariant s == \at(m, Pre);

    loop invariant l == (\at(b, Pre) % 15) + 18;

    loop invariant q == n + (i/2) * s;

    loop invariant i <= l + 1;

    loop invariant l == (b % 15) + 18;

    loop invariant q - n == s * (i/2);

    loop invariant q == n + s * (i/2);

    loop invariant s == m;

    loop invariant l == (\at(b,Pre) % 15) + 18;

    loop invariant i >= 0;


    loop invariant q == n + m * (i/2);

    loop invariant b == \at(b,Pre);

    loop invariant k == \at(k,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant n == \at(n,Pre);

    loop invariant 0 <= i <= l + 1;

    loop assigns q, i;

    loop variant l - i;

  */
while (i<l) {
      q = q+s;
      i = i+2;
  }

}