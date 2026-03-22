int main1(){
  int fue, i5v, m8, e1, frd;
  fue=1-8;
  i5v=0;
  m8=0;
  e1=i5v;
  frd=fue;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m8 >= 0;
  loop invariant frd == fue;
  loop invariant e1 == i5v * (m8 + 1);
  loop invariant e1 == m8 * i5v;
  loop assigns m8, frd, e1;
*/
while (m8<fue) {
      m8 = m8 + 1;
      if (m8<=frd) {
          frd = m8;
      }
      e1 += i5v;
  }
}