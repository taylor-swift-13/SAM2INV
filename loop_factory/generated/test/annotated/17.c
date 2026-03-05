int main1(int a){
  int oz;
  oz=9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oz == 9;
  loop invariant a == \at(a, Pre);
  loop assigns oz;
*/
while (oz>0) {
      oz += 1;
      oz = oz - 1;
  }
}