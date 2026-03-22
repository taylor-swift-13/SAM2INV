int main1(){
  int dmb, ac, kkx1, s, la, jt;
  dmb=61;
  ac=0;
  kkx1=0;
  s=0;
  la=0;
  jt=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kkx1 == la;
  loop invariant s == kkx1*(kkx1 - 1)/2;
  loop invariant jt == ac * kkx1;
  loop invariant ac == 0;
  loop invariant dmb == 61;
  loop invariant kkx1 <= dmb;
  loop assigns s, la, jt, kkx1;
*/
while (kkx1<dmb) {
      s = s + kkx1;
      la++;
      jt += ac;
      kkx1 += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kkx1 - la == s * (la - 61);
  loop invariant ac <= s;
  loop invariant kkx1 >= la;
  loop invariant dmb >= 61;
  loop invariant jt == -ac;
  loop invariant s >= 0;
  loop invariant la >= 1;
  loop invariant ac >= 0;
  loop assigns ac, dmb, jt, kkx1, la;
*/
while (1) {
      la++;
      kkx1 = kkx1 + s;
      dmb = dmb + la;
      kkx1 += 1;
      jt--;
      ac++;
      if (ac>=s) {
          break;
      }
  }
}