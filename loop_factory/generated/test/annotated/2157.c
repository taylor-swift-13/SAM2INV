int main1(){
  int ijg9, wx, rc6, qa, xe6;
  ijg9=1+17;
  wx=0;
  rc6=1;
  qa=0;
  xe6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rc6 == qa + 1;
  loop invariant xe6 * 2 == qa * (qa + 3);
  loop invariant 0 <= qa;
  loop invariant wx <= ijg9;
  loop invariant (wx < ijg9) ==> (qa < ijg9);
  loop invariant wx >= qa;
  loop invariant (wx < ijg9) ==> ((ijg9 - wx + rc6 - 1) / rc6 >= 1);
  loop invariant xe6 == ((rc6 * (rc6 + 1)) / 2) - 1;
  loop assigns wx, rc6, xe6, qa;
*/
while (wx < ijg9) {
      wx = wx + (ijg9 - wx + rc6 - 1) / rc6;
      rc6 = rc6 + 1;
      xe6 = xe6 + rc6;
      qa = qa + 1;
  }
}