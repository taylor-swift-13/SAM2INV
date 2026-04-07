int main1(int j){
  int p78, qy, r1d0, ie;
  p78=60;
  qy=0;
  r1d0=0;
  ie=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= qy;
  loop invariant qy <= p78;
  loop invariant r1d0 == - ie * qy;
  loop invariant j == \at(j, Pre);
  loop invariant ie == 2;
  loop invariant p78 == 60;
  loop assigns qy, r1d0, j;
*/
while (1) {
      if (!(qy < p78)) {
          break;
      }
      qy = qy + 1;
      r1d0 -= ie;
      j = j+r1d0-r1d0;
  }
}