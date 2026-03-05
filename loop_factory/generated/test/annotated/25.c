int main1(){
  int rq;
  rq=-3770;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rq <= -3770;
  loop invariant rq % 2 == 0;
  loop assigns rq;
*/
while (rq+8<0) {
      rq = rq+rq+2;
      rq += 2;
  }
}