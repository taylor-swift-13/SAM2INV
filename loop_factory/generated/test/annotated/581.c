int main1(){
  int i, m5, tm;
  i=1+8;
  m5=1;
  tm=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 9;
  loop invariant (tm == 0 && m5 == 1) || (tm == 1 && m5 == 2) || (tm == 2 && m5 == 4) || (tm == 3 && m5 == 8) || (tm == 4 && m5 == 16);
  loop assigns tm, m5;
*/
while (m5<=i) {
      tm = tm + 1;
      m5 = 2*m5;
  }
}