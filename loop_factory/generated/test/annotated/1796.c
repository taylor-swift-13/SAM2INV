int main1(){
  int hvx7, fkju, dle, m, oy8, v;
  hvx7=1+15;
  fkju=5;
  dle=fkju;
  m=3;
  oy8=25;
  v=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m % v == 0;
  loop invariant hvx7 == 16;
  loop invariant oy8 >= 25;
  loop invariant m >= 3;
  loop invariant 6*dle == 11*m - 3;
  loop assigns oy8, dle, m;
*/
while (1) {
      if (oy8>=hvx7) {
          break;
      }
      oy8 = oy8 + 1;
      dle = dle*v+1;
      m = m*v;
  }
}