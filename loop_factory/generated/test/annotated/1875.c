int main1(){
  int y1, sok, qd2s, i5, d1, bg, zv, z0;
  y1=14;
  sok=2;
  qd2s=-5;
  i5=sok;
  d1=sok;
  bg=5;
  zv=0;
  z0=sok;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sok <= y1;
  loop invariant qd2s - i5 == -7;
  loop invariant i5 >= 2;
  loop invariant d1 >= 2;
  loop invariant bg >= 5;
  loop invariant zv >= 0;
  loop invariant z0 == 2;
  loop invariant y1 == 14;
  loop assigns qd2s, i5, bg, d1, z0, zv, sok;
*/
while (1) {
      if (!(sok < y1)) {
          break;
      }
      if (!(!(sok < y1/2))) {
          qd2s = qd2s + 1;
          i5 += 1;
      }
      else {
          qd2s += 2;
          i5 += 2;
      }
      if ((sok%2)==0) {
          bg = bg + 1;
      }
      d1 += 1;
      z0 = z0+qd2s-qd2s;
      zv += i5;
      sok = y1;
      if ((sok%7)==0) {
          zv = zv + sok;
      }
  }
}