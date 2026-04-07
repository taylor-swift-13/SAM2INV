int main1(int m){
  int wfv, mg4, ki, e;
  wfv=m;
  mg4=0;
  ki=m;
  e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ki + mg4 == wfv;
  loop invariant mg4 >= 0 && (\at(m, Pre) >= 0 ==> mg4 <= \at(m, Pre));
  loop invariant wfv == \at(m, Pre);
  loop invariant e == (mg4 * \at(m, Pre) - (mg4 * (mg4 + 1)) / 2);
  loop invariant ki <= m;
  loop assigns mg4, ki, e;
*/
while (1) {
      if (!(mg4 < wfv)) {
          break;
      }
      mg4 = mg4 + 1;
      ki = ki - 1;
      e += ki;
  }
}