int main1(int h){
  int bx, m, ep;
  bx=h;
  m=0;
  ep=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ep >= 4;
  loop invariant ep % 2 == 0;
  loop invariant m == 0;
  loop invariant (ep + 6) % 10 == 0;
  loop assigns ep;
*/
while (m+5<=bx) {
      ep = ep + 3;
      ep = ep + ep;
  }
}