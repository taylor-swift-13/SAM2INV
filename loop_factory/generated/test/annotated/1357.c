int main1(){
  int c, tp;
  c=1-2;
  tp=c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == 1 - 2;
  loop invariant tp <= c;
  loop invariant tp % 4 == c % 4;
  loop assigns tp;
*/
for (; tp>=4; tp -= 4) {
  }
}