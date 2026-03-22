int main1(int a){
  int hl, bi, rxax, d, g2q0;
  hl=a+25;
  bi=0;
  rxax=1;
  d=0;
  g2q0=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g2q0 == d;
  loop invariant hl == a + 25;
  loop invariant bi >= 0;
  loop invariant (hl < 0) || (bi <= hl);
  loop assigns bi, rxax, g2q0, d;
*/
while (1) {
      if (!(bi < hl)) {
          break;
      }
      bi += 1;
      rxax = rxax * a;
      g2q0 = g2q0 + rxax;
      d = d + rxax;
  }
}