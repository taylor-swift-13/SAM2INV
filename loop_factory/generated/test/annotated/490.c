int main1(){
  int hrz, e, sam1, bsc, p6, kmwo;
  hrz=(1%14)+19;
  e=0;
  sam1=0;
  bsc=0;
  p6=(1%18)+5;
  kmwo=hrz;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == sam1;
  loop invariant bsc == sam1;
  loop invariant kmwo == hrz + sam1*(sam1+1)/2;
  loop invariant p6 + sam1 == 6;
  loop invariant 0 <= sam1;
  loop invariant sam1 <= 6;
  loop assigns sam1, e, p6, bsc, kmwo;
*/
while (1) {
      if (!(p6>=1)) {
          break;
      }
      sam1 = sam1+1*1;
      e = e+1*1;
      p6 = (p6)+(-(1));
      bsc = bsc+1*1;
      kmwo += bsc;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p6 == - ((sam1 - 6) * (sam1 + 5)) / 2;
  loop invariant kmwo == 3*sam1 + 23;
  loop invariant kmwo - 3*sam1 == hrz + 3;
  loop invariant p6 <= sam1;
  loop invariant 0 <= sam1;
  loop assigns p6, sam1, bsc, kmwo;
*/
while (1) {
      if (!(p6>sam1)) {
          break;
      }
      p6 -= sam1;
      sam1++;
      kmwo = kmwo + 3;
      bsc = bsc+(p6%9);
  }
}