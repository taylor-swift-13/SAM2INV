int main1(int a,int b,int m,int q){
  int l, i, v, o;

  l=(b%12)+15;
  i=0;
  v=a;
  o=l;

  
  /*@

    loop invariant 0 <= i <= l;

    loop invariant l == (\at(b, Pre) % 12) + 15;

    loop invariant o == l + 5*i;

    loop invariant v == a + 5*i + i*(i-1)/2;

    loop invariant l == (b % 12) + 15;

    loop invariant i <= l;

    loop invariant a == \at(a, Pre);

    loop invariant i >= 0;

    loop invariant v == a + 5*i + (i * (i - 1)) / 2;

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant l == (\at(b,Pre) % 12) + 15;

    loop invariant a == \at(a,Pre);

    loop invariant b == \at(b,Pre);

    loop assigns v, o, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+5;
      o = o+4;
      o = o+1;
      v = v+i;
      i = i+1;
  }

}