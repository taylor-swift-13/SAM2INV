int main1(){
  int s5d, og, gim, g2, a;
  s5d=1*4;
  og=1;
  gim=0;
  g2=3;
  a=og;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g2 >= gim + 3;
  loop invariant a <= 1;
  loop invariant g2 == 3 + (gim/2) * ((gim/2) + 1);
  loop invariant (gim % 2) == 0;
  loop invariant (0 <= gim && gim <= s5d);
  loop assigns gim, g2, a;
*/
while (gim<s5d) {
      gim += 2;
      if (!(!(gim<=a))) {
          a = gim;
      }
      g2 = g2 + gim;
  }
}