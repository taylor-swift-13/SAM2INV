int main1(){
  int ivns, tf0d, a7, bh, g;
  ivns=56;
  tf0d=ivns+6;
  a7=0;
  bh=12;
  g=13;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a7 == 0;
  loop invariant ((g == 13) || (g == bh * bh));
  loop invariant ivns == 56;
  loop invariant (1 <= tf0d && tf0d <= 62);
  loop invariant (0 <= bh && bh <= 12);
  loop invariant (0 <= g && g <= 144);
  loop assigns a7, bh, g, tf0d;
*/
while (1) {
      if (!(tf0d>1)) {
          break;
      }
      a7 = a7*4;
      bh = bh/4;
      g = bh*bh;
      tf0d = tf0d/2;
  }
}