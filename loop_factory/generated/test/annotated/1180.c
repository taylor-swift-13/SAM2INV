int main1(int u){
  int to, n3, zhv, rc, rct;
  to=(u%60)+60;
  n3=(u%9)+2;
  zhv=0;
  rc=0;
  rct=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zhv >= 0;
  loop invariant rct >= 11;
  loop invariant (to - (n3 * zhv + rc)) >= 0;
  loop assigns rc, zhv, rct;
*/
while (1) {
      if (to<=n3*zhv+rc) {
          break;
      }
      if (rc==n3-1) {
          rc = 0;
          zhv += 1;
      }
      else {
          rc = rc + 1;
      }
      rct = rct+(zhv%6);
  }
}