int main1(int b,int n){
  int m, t, e, c;

  m=(b%38)+12;
  t=0;
  e=0;
  c=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(b, Pre) % 38 + 12;
  loop invariant n == \at(n, Pre);
  loop invariant t == 0;
  loop invariant e == c + t || c == \at(b, Pre);
  loop invariant m == (b % 38) + 12;
  loop invariant -25 <= m <= 49;
  loop invariant (c == \at(b, Pre) && e == 0) || (e == c + t);
  loop invariant m == ((\at(b, Pre) % 38) + 12);
  loop assigns c, e;
*/
while (1) {
      c = m-e;
      e = e+1;
      e = e+c;
      c = c+c;
      c = c+4;
      e = c+t;
  }

}
