int main1(){
  int nun5, whsx, rl;
  nun5=1+22;
  whsx=0;
  rl=nun5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rl >= nun5;
  loop invariant (whsx == 0) ==> (rl == nun5);
  loop invariant (whsx > 0) ==> (rl % 2 == 0);
  loop invariant 0 <= whsx;
  loop invariant whsx <= nun5;
  loop invariant nun5 == 23;
  loop assigns rl, whsx;
*/
while (1) {
      if (!(whsx<nun5)) {
          break;
      }
      if (whsx>=nun5/2) {
          rl += 4;
      }
      rl += rl;
      whsx += 1;
  }
}