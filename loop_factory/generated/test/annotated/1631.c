int main1(int f){
  int hw8, a38a, t2l6;
  hw8=0;
  a38a=70;
  t2l6=35;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a38a == 2 * t2l6;
  loop invariant t2l6 >= 0;
  loop invariant a38a + hw8 == 70;
  loop assigns a38a, t2l6, hw8;
*/
while (t2l6>=1) {
      a38a -= 2;
      t2l6 -= 1;
      hw8 += 2;
  }
}