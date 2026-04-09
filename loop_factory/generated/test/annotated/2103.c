int main1(){
  int khn, y, ch, m6;
  khn=(1%38)+11;
  y=0;
  ch=0;
  m6=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= y;
  loop invariant y <= khn;
  loop invariant khn == (1 % 38) + 11;
  loop invariant (y == 0  ==> (ch == 0     && m6 == -2))  &&
       (y == 1  ==> (ch == -2    && m6 == -4))  &&
       (y == 2  ==> (ch == -6    && m6 == -10)) &&
       (y == 3  ==> (ch == -16   && m6 == -26)) &&
       (y == 4  ==> (ch == -42   && m6 == -68)) &&
       (y == 5  ==> (ch == -110  && m6 == -178))&&
       (y == 6  ==> (ch == -288  && m6 == -466))&&
       (y == 7  ==> (ch == -754  && m6 == -1220))&&
       (y == 8  ==> (ch == -1974 && m6 == -3194))&&
       (y == 9  ==> (ch == -5168 && m6 == -8362))&&
       (y == 10 ==> (ch == -13530&& m6 == -21892))&&
       (y == 11 ==> (ch == -35422&& m6 == -57314))&&
       (y == 12 ==> (ch == -92736&& m6 == -150050));
  loop invariant ch <= 0;
  loop invariant m6 <= -2;
  loop invariant m6 < ch;
  loop assigns y, ch, m6;
*/
while (y < khn) {
      y++;
      ch = ch + m6;
      m6 = m6 + ch;
  }
}