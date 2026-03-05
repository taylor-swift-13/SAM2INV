int main1(int t){
  int a7r6, ft7;
  a7r6=19;
  ft7=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a7r6 == 19;
  loop invariant ft7 >= 0;
  loop invariant t == \at(t, Pre);
  loop invariant ft7 <= 2*a7r6 + 2;
  loop invariant (ft7 % 2 == 0);
  loop assigns ft7;
*/
while (ft7<=a7r6) {
      ft7 = ft7 + 1;
      ft7 = ft7 + ft7;
  }
}