int main1(int a,int b,int k,int m){
  int l, i, v, g;

  l=(k%14)+18;
  i=0;
  v=l;
  g=m;

  
  /*@

    loop invariant v == (\at(k, Pre) % 14 + 18) + 7 * i;

    loop invariant g == \at(m, Pre) + i * (\at(k, Pre) % 14 + 19) + (7 * i * (i - 1)) / 2;

    loop invariant 0 <= i && i <= l;

    loop invariant l == (\at(k, Pre) % 14 + 18);

    loop invariant k == \at(k, Pre) && m == \at(m, Pre);

    loop invariant i <= l;

    loop invariant v == l + 7*i;

    loop invariant g == \at(m, Pre) + i*(l+1) + 7*i*(i-1)/2;

    loop invariant l == (\at(k, Pre) % 14) + 18;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant i >= 0;

    loop invariant g == m + i*(l + 1) + 7*(i*(i - 1)/2);

    loop invariant g == m + i*(l+1) + 7*i*(i-1)/2;

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && k == \at(k, Pre) && m == \at(m, Pre);

    loop invariant 0 <= i <= l;

    loop invariant g == m + i*(l+1) + 7*(i*(i-1))/2;

    loop invariant l == (k % 14) + 18;

    loop assigns i, v, g;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      g = g+v;
      v = v+6;
      i = i+1;
  }

}