int main1(){
  int q, gg, qxmf, d, t;
  q=(1%6)+4;
  gg=1;
  qxmf=0;
  d=0;
  t=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == gg - 1;
  loop invariant d == (gg - 1) % 8;
  loop invariant qxmf == (gg - 1) / 8;
  loop invariant 0 <= d <= 7;
  loop invariant 1 <= gg <= q;
  loop invariant q == (1 % 6) + 4;
  loop assigns d, t, qxmf, gg;
*/
while (1) {
      if (!(gg<q)) {
          break;
      }
      d++;
      t += 1;
      if (d>=8) {
          d -= 8;
          qxmf = qxmf + 1;
      }
      gg += 1;
  }
}