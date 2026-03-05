int main1(int c){
  int ajck, tb4j;
  ajck=c;
  tb4j=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tb4j % 2 == 0;
  loop invariant tb4j >= 0;
  loop invariant c == \at(c, Pre) + (tb4j/2) * (tb4j/2 + 1);
  loop invariant ajck == \at(c, Pre);
  loop invariant c - \at(c, Pre) == tb4j*(tb4j+2)/4;
  loop invariant 0 <= tb4j;
  loop invariant 0 <= c - \at(c, Pre);
  loop assigns tb4j, c;
*/
while (tb4j<ajck) {
      tb4j += 2;
      c += tb4j;
  }
}