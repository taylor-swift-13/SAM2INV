int main1(){
  int q7q, czk4, re, x6, t, dk;
  q7q=79;
  czk4=0;
  re=0;
  x6=1;
  t=1;
  dk=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= czk4 <= q7q;
  loop invariant re == czk4 * dk;
  loop invariant t == 1 + czk4 * (czk4 + 1) / 2;
  loop invariant x6 >= 1;
  loop invariant re == czk4;
  loop assigns x6, czk4, re, t;
*/
while (1) {
      if (!(czk4 < q7q)) {
          break;
      }
      x6 = x6 * t;
      czk4 += 1;
      re = re + dk;
      t += czk4;
  }
}