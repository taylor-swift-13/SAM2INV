int main1(){
  int b0, fd, t8, yk1, th7;
  b0=10;
  fd=0;
  t8=0;
  yk1=4;
  th7=fd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= fd;
  loop invariant fd <= b0;
  loop invariant 2 * th7 == fd + t8;
  loop invariant (t8 == 0) || (t8 == 1);
  loop invariant yk1 >= 4;
  loop invariant th7 == (fd + 1) / 2;
  loop assigns t8, fd, th7, yk1;
*/
while (fd < b0) {
      t8 = 1 - t8;
      fd++;
      th7 += t8;
      yk1 = yk1*yk1+yk1;
  }
}