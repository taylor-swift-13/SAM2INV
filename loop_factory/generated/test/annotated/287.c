int main1(int l){
  int mi, s6;
  mi=79;
  s6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= s6;
  loop invariant s6 <= mi;
  loop invariant mi == 79;
  loop assigns s6;
*/
while (1) {
      s6++;
      if (s6>=mi) {
          break;
      }
  }
}