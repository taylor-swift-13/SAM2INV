int main1(int p){
  int vou, cc, m55, gp9;
  vou=p-9;
  cc=vou;
  m55=3;
  gp9=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m55 - cc <= 3 - vou;
  loop invariant cc <= vou;
  loop invariant gp9 == 1 || gp9 == -1;
  loop invariant vou == p - 9;
  loop invariant (3 <= m55 <= 10) && ((m55 <= 3) ==> (gp9 == 1)) && ((m55 >= 10) ==> (gp9 == -1));
  loop assigns cc, m55, gp9;
*/
while (cc<vou) {
      if (!(m55<10)) {
          gp9 = -1;
      }
      if (m55<=3) {
          gp9 = 1;
      }
      m55 += gp9;
      cc = cc + 1;
  }
}