int main1(int j){
  int aops, hbz, zm;
  aops=j;
  hbz=0;
  zm=hbz;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == \at(j, Pre) + 3*hbz;
  loop invariant hbz >= 0;
  loop invariant aops == \at(j, Pre);
  loop invariant zm == hbz*aops - (hbz*(hbz+1))/2;
  loop assigns hbz, j, zm;
*/
while (hbz < aops) {
      hbz = hbz + 1;
      j = j + 3;
      zm = zm+aops-hbz;
  }
}