int main1(int c){
  int vo, j, s;
  vo=(c%32)+13;
  j=0;
  s=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vo == \at(c, Pre) % 32 + 13;
  loop invariant j >= 0;
  loop invariant (vo > 0) ==> (j <= vo);
  loop invariant s == -8 + 3 * j;
  loop invariant c == \at(c, Pre) + (-8) * j + 3 * j * (j - 1) / 2;
  loop invariant (vo >= 0) ==> (j <= vo);
  loop invariant (2*(c - \at(c, Pre)) == (-16*j + 3*j*(j-1)));
  loop invariant ((\at(c, Pre) % 32 + 13) >= 0) ==> (j <= vo);
  loop assigns c, j, s;
*/
while (j < vo) {
      c = c + s;
      j++;
      s = s + 3;
  }
}