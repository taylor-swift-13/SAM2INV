int main1(int e){
  int ah, y, w33, z, qf;
  ah=10;
  y=0;
  w33=y;
  z=2;
  qf=25;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= y;
  loop invariant y <= ah;
  loop invariant 2 * w33 == y * (y - 1);
  loop invariant 6 * (qf - 25) == (y * (y - 1) * (y + 1));
  loop invariant 24 * (z - 2 - y * (25 + \at(e, Pre))) == (y * (y - 1) * (y + 1) * (y + 2));
  loop invariant e == \at(e, Pre);
  loop invariant ah == 10;
  loop assigns w33, y, qf, z;
*/
while (y < ah) {
      w33 = w33 + y;
      y++;
      qf = qf + w33;
      z = z+qf+e;
  }
}