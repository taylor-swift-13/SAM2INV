int main1(){
  int j2, sc, qs, xk, ucy;
  j2=1+5;
  sc=0;
  qs=j2;
  xk=j2;
  ucy=qs;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j2 == 1 + 5;
  loop invariant qs == j2;
  loop invariant ucy == qs;
  loop invariant 0 <= sc;
  loop invariant sc <= j2;
  loop invariant sc == 0 || sc == j2;
  loop invariant (sc == 0 && xk == j2) || (sc == j2 && xk == 2 * j2);
  loop invariant (xk == qs || xk == qs + j2);
  loop invariant (sc == j2) <==> (xk == qs + j2);
  loop invariant xk >= j2;
  loop invariant xk <= 2 * j2;
  loop invariant (xk % j2) == 0;
  loop assigns sc, ucy, xk;
*/
while (1) {
      if (!(sc < j2)) {
          break;
      }
      ucy = (sc++, (ucy < qs ? ucy : qs));
      xk += j2;
      sc = j2;
  }
}