int main1(int e){
  int qtt, j, vl8, wg;
  qtt=e+3;
  j=0;
  vl8=qtt;
  wg=qtt;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((j == 0 && vl8 == qtt && wg == qtt) ||
                    (j == qtt && vl8 == qtt - 1 && wg == qtt + 1));
  loop invariant vl8 + wg == 2 * qtt;
  loop invariant qtt == e + 3;
  loop invariant (j == 0) ==> (vl8 == qtt);
  loop invariant (j == 0) ==> (wg == qtt);
  loop invariant (j != 0) ==> (vl8 == qtt - 1);
  loop invariant (j != 0) ==> (wg == qtt + 1);
  loop invariant (j == 0) || (j == qtt);
  loop assigns vl8, wg, j;
*/
while (1) {
      if (!(j < qtt)) {
          break;
      }
      vl8--;
      wg = wg + 1;
      j = qtt;
  }
}