int main1(){
  int i50, u4, zpg9, hbe, l1;
  i50=72;
  u4=0;
  zpg9=-2;
  hbe=i50;
  l1=i50;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= u4;
  loop invariant u4 <= i50;
  loop invariant i50 == 72;
  loop invariant hbe >= 72;
  loop invariant l1 >= 72;
  loop invariant zpg9 >= -2;
  loop invariant (hbe % 2) == 0;
  loop invariant (l1 % 2) == 0;
  loop invariant (zpg9 % 2) == 0;
  loop invariant zpg9 < l1;
  loop assigns zpg9, hbe, u4, l1;
*/
while (1) {
      if (!(u4 < i50)) {
          break;
      }
      zpg9 = zpg9 + hbe;
      hbe = hbe + l1;
      u4++;
      l1 += zpg9;
  }
}