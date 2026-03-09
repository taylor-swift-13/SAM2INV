int main1(){
  int vrts, ynk, hs, su;
  vrts=(1%29)+6;
  ynk=0;
  hs=0;
  su=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant su + ynk == 4;
  loop invariant 0 <= su;
  loop invariant hs >= 0;
  loop invariant hs % 2 == 0;
  loop invariant 0 <= ynk <= vrts;
  loop assigns ynk, hs, su;
*/
while (1) {
      if (!(ynk<vrts&&su>0)) {
          break;
      }
      ynk += 1;
      hs += su;
      hs = hs + hs;
      su -= 1;
  }
}