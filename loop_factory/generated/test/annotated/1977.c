int main1(int j){
  int uc1, uu, afe;
  uc1=14;
  uu=0;
  afe=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uu <= 19;
  loop invariant 0 <= afe;
  loop invariant afe <= uu;
  loop invariant uc1 == 14 + 32*uu - 36*afe;
  loop assigns uc1, afe, uu;
*/
while (1) {
      if (!(uu<=18)) {
          break;
      }
      if (!(uc1>=0)) {
          uc1 = uc1+-4;
          afe = afe + 1;
      }
      else {
          uc1 = uc1 + 32;
      }
      uu = uu + 1;
  }
}