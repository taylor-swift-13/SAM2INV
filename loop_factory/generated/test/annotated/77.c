int main1(){
  int tz, yk6;
  tz=61;
  yk6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yk6 >= 0;
  loop invariant yk6 % 2 == 0;
  loop invariant yk6 <= 2*tz;
  loop assigns yk6;
*/
while (yk6<tz) {
      yk6 = yk6 + 1;
      if (yk6<=yk6) {
          yk6 = yk6;
      }
      yk6 += yk6;
  }
}