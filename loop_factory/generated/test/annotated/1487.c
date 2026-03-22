int main1(){
  int x, c4, x3, jb;
  x=147;
  c4=0;
  x3=6;
  jb=x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c4 == 0;
  loop invariant (c4 + 7 <= x) ==> jb == x;
  loop invariant x == 147 || x == c4 + 6;
  loop invariant jb == 147 || jb == 294;
  loop invariant jb == 147 * (x3 - 5);
  loop assigns x3, jb, x;
*/
while (c4+7<=x) {
      x3 = x3 + 1;
      jb += x;
      x = (c4+7)-1;
  }
}