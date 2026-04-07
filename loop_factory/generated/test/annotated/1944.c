int main1(){
  int eyn, m0s, y, is3;
  eyn=1-3;
  m0s=0;
  y=20;
  is3=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant is3 == m0s;
  loop invariant m0s >= 0;
  loop invariant 2*(y - 20) == m0s*(m0s + 1);
  loop invariant y == 20 + (m0s * (m0s + 1)) / 2;
  loop assigns m0s, is3, y;
*/
while (m0s < eyn) {
      m0s += 1;
      is3 = m0s;
      y += m0s;
  }
}