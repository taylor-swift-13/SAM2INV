int main1(int a,int b,int m,int q){
  int l, i, v, o;

  l=(b%12)+15;
  i=0;
  v=a;
  o=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == a + 5*i;
    loop invariant o == l + 4*i;
    loop invariant i <= l;
    loop invariant l == ((\at(b,Pre) % 12) + 15);
    loop invariant a == \at(a,Pre);
    loop invariant b == \at(b,Pre);
    loop invariant m == \at(m,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant 0 <= i <= l;
    loop invariant l == (b % 12) + 15;
    loop invariant a == \at(a, Pre);
    loop invariant b == \at(b, Pre);
    loop invariant 0 <= i;
    loop invariant v == \at(a, Pre) + 5*i;
    loop invariant l == ((\at(b, Pre) % 12) + 15);
    loop invariant (a == \at(a, Pre) && b == \at(b, Pre) && m == \at(m, Pre) && q == \at(q, Pre));
    loop invariant i >= 0;
    loop invariant m == \at(m, Pre);
    loop invariant q == \at(q, Pre);
    loop assigns v, o, i;
  */
  while (i<l) {
      v = v+5;
      o = o+4;
      i = i+1;
  }

}