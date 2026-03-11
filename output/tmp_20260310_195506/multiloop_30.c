int main1(){
  int dqf, g4l, sgm, mm;
  dqf=1;
  g4l=0;
  sgm=-8;
  mm=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dqf == 1;
  loop invariant g4l == 0;
  loop invariant mm == 4;
  loop invariant -8 <= sgm <= dqf;
  loop assigns sgm, mm;
*/
while (sgm<dqf) {
      if (sgm<dqf/2) {
          sgm += 2;
      }
      else {
          sgm = sgm + 1;
      }
      mm = mm + g4l;
  }

  int __aux_loop = 0;
  while (__aux_loop < 2) {
      __aux_loop = __aux_loop + 1;
  }
/*@
  assert !(__aux_loop < 2) &&
         (dqf == 1);
*/

}