int main1(int k){
  int odt, k4dg, ncc, rd, b89, xp;
  odt=k*4;
  k4dg=1;
  ncc=0;
  rd=0;
  b89=k;
  xp=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ncc == k * rd;
  loop invariant b89 == k + rd;
  loop invariant odt == 4 * k;
  loop invariant k4dg == 1;
  loop assigns ncc, b89, rd;
*/
while (rd<odt) {
      ncc = ncc + k;
      b89 += k4dg;
      rd++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xp == -1 || xp == 0;
  loop invariant odt == 4 * k;
  loop assigns b89, rd, xp;
*/
while (1) {
      if (!(xp>=1)) {
          break;
      }
      b89 = b89+rd*xp;
      rd = rd + b89;
      xp = 0;
  }
}