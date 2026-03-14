int main1(int k){
  int ral2, fr, ct91, uave;
  ral2=80;
  fr=1;
  ct91=0;
  uave=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fr <= ral2;
  loop invariant uave == ct91 + 2;
  loop invariant uave == 2*fr;
  loop assigns uave, fr, ct91;
*/
while (1) {
      if (!(fr<ral2)) {
          break;
      }
      uave += 2;
      fr = fr + 1;
      ct91 += 2;
  }
}