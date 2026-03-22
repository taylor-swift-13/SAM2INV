int main1(int n,int m){
  int y, ik;
  y=166;
  ik=y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ik % 3 == 1);
  loop invariant ik >= 1;
  loop invariant y == 166;
  loop invariant ik <= 166;
  loop assigns ik;
*/
for (; ik>=3; ik = ik - 3) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ik >= 0);
  loop invariant y == 166;
  loop invariant (ik <= 1);
  loop assigns ik;
*/
while (1) {
      if (!(ik>=1)) {
          break;
      }
      ik = ik - 1;
  }
}