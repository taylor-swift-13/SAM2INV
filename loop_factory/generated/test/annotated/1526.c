int main1(){
  int g, q1, w8h, yax, op, m5, p59, x;
  g=1;
  q1=0;
  w8h=0;
  yax=q1;
  op=q1;
  m5=12;
  p59=q1;
  x=g;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= p59;
  loop invariant 0 <= m5;
  loop invariant 0 <= w8h <= q1;
  loop invariant 0 <= yax <= q1;
  loop invariant 0 <= op <= q1;
  loop invariant w8h + yax == q1;
  loop invariant 0 <= q1 <= g;
  loop invariant g == 1;
  loop invariant 0 <= x;
  loop invariant x <= 8;
  loop assigns w8h, yax, op, m5, x, p59, q1;
*/
while (1) {
      if (q1%4==1) {
          w8h = w8h + 1;
      }
      else {
          yax += 1;
      }
      if (q1%4==2) {
          op++;
      }
      else {
      }
      m5 = m5 + 1;
      x = (x+w8h)%9;
      p59 += m5;
      m5 = p59-m5;
      q1 = q1 + 1;
      if (q1>=g) {
          break;
      }
  }
}