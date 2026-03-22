int main1(int d){
  int t8, jr, w4, qf3;
  t8=128;
  jr=0;
  w4=0;
  qf3=jr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == \at(d,Pre) + (w4*(w4+1))/2;
  loop invariant (w4 == 0 && qf3 == 0) || (qf3 == w4 + 2);
  loop invariant 0 <= w4 <= t8;
  loop assigns d, qf3, w4;
*/
while (w4<=t8-1) {
      qf3 = w4+3;
      w4 = w4 + 1;
      d = d + w4;
  }
}