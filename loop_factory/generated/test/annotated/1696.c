int main1(){
  int u, hj, ljo, tcg;
  u=1;
  hj=0;
  ljo=0;
  tcg=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ljo == hj;
  loop invariant hj <= u;
  loop invariant 0 <= hj;
  loop invariant 0 <= tcg;
  loop invariant tcg <= 2*u;
  loop assigns ljo, hj, tcg;
*/
while (1) {
      if (!(hj < u)) {
          break;
      }
      ljo = ((ljo + 1) > u) ? u : (ljo + 1);
      hj = hj + 1;
      tcg = ((tcg + 1) > u) ? u : (tcg + 1);
      tcg += tcg;
  }
}