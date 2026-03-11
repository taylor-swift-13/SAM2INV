int main1(int c){
  int bd0, y5f;
  bd0=(c%20)+12;
  y5f=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bd0 == (\at(c, Pre) % 20) + 12;
  loop invariant c == \at(c, Pre);
  loop invariant y5f >= 0 && ((bd0 <= 0) || (y5f <= bd0));
  loop assigns y5f;
*/
while (1) {
      y5f = y5f + 1;
      if (y5f>=bd0) {
          break;
      }
  }
}