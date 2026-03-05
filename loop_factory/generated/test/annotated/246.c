int main1(){
  int j, ki;
  j=1;
  ki=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 1;
  loop invariant ki == 0;
  loop invariant ki <= j - 1;
  loop assigns ki;
*/
while (ki<j) {
      if (ki<j/2) {
          ki += 1;
      }
      else {
          ki = ki - 1;
      }
      ki += 1;
      ki += ki;
  }
}