int main1(){
  int zydq, ji, rw, o7, kin7;
  zydq=(1%27)+19;
  ji=0;
  rw=0;
  o7=0;
  kin7=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kin7 + rw == 6;
  loop invariant o7 == rw;
  loop invariant ji >= 0;
  loop invariant ji % 2 == 0;
  loop invariant 0 <= kin7 <= 6;
  loop invariant zydq == 20;
  loop assigns kin7, rw, ji, o7;
*/
while (kin7>0) {
      kin7 = kin7 - 1;
      rw = rw+1*1;
      ji = ji+1*1;
      o7 = o7+1*1;
      ji = ji*2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zydq >= 20;
  loop invariant kin7 >= 0;
  loop invariant rw >= 0;
  loop assigns rw, kin7, zydq;
*/
while (rw>kin7) {
      rw = rw - kin7;
      kin7 += 1;
      zydq = zydq + rw;
      zydq = zydq*3+1;
  }
}