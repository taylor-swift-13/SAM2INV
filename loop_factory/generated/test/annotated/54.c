int main1(){
  int n39, ttt;
  n39=1;
  ttt=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= ttt) && (ttt <= n39) && (n39 == 1) && ((ttt == 0) || (ttt % 2 == 1));
  loop assigns ttt;
*/
while (ttt<n39) {
      ttt = 2*ttt;
      ttt = ttt + 1;
  }
}