int main1(int y){
  int fk0, svma, kgh, tz;
  fk0=y*5;
  svma=0;
  kgh=0;
  tz=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fk0 == 5*y;
  loop invariant fk0 == \at(y, Pre) * 5;
  loop invariant kgh == 4*svma - (svma*(svma - 1))/2;
  loop invariant svma >= 0;
  loop invariant tz >= 0;
  loop invariant tz == 4 - svma;
  loop assigns svma, kgh, tz;
*/
while (svma<fk0&&tz>0) {
      svma++;
      kgh += tz;
      tz -= 1;
  }
}