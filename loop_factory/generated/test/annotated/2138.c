int main1(int m){
  int wpo4, zbr, gib, in7, b;
  wpo4=m;
  zbr=m;
  gib=wpo4;
  in7=7;
  b=(m%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wpo4 == \at(m, Pre);
  loop invariant b == ((\at(m, Pre) % 6) + 2);
  loop invariant gib == ((zbr - gib) * (b - 1)) + \at(m, Pre);
  loop invariant in7 >= 7 && (in7 <= wpo4 || wpo4 < 7);
  loop invariant wpo4 == m;
  loop assigns zbr, gib, in7;
*/
while (1) {
      if (in7>=wpo4) {
          break;
      }
      zbr = zbr*b+m;
      gib = gib*b;
      in7 = in7 + 1;
  }
}