int main1(){
  int m8, na;
  m8=1+15;
  na=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m8 == 16;
  loop invariant 0 <= na;
  loop invariant na <= m8 - 1;
  loop assigns na;
*/
while (na<m8) {
      if (na<m8/2) {
          na += 2;
      }
      else {
          na -= 2;
      }
      na = na + 1;
  }
}