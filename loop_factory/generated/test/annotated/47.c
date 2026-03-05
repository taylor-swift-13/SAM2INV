int main1(int s){
  int yoxr, et5n;
  yoxr=9;
  et5n=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant et5n % 6 == 0;
  loop invariant 0 <= et5n;
  loop invariant s == \at(s, Pre);
  loop invariant yoxr == 9;
  loop invariant et5n < yoxr + 6;
  loop assigns et5n;
*/
while (et5n<yoxr) {
      et5n = et5n + 5;
      et5n += 1;
  }
}