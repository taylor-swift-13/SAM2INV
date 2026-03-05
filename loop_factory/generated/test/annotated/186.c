int main1(int y,int h){
  int r9ey, qjhc, oq, vw5;
  r9ey=59;
  qjhc=0;
  oq=-1;
  vw5=qjhc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vw5 >= 0;
  loop invariant h == \at(h, Pre);
  loop invariant qjhc == 0;
  loop invariant r9ey == 59;
  loop invariant y == \at(y, Pre) + vw5 * r9ey;
  loop invariant (vw5 == 0) ==> (oq == -1);
  loop invariant (vw5 > 0) ==> (oq == vw5 * vw5);
  loop assigns vw5, oq, y;
*/
while (qjhc+1<=r9ey) {
      vw5 += 1;
      oq = vw5*vw5;
      y = y + r9ey;
  }
}