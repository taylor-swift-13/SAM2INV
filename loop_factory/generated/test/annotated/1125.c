int main1(){
  int iwn, qdia, i5, i;
  iwn=1;
  qdia=(1%40)+2;
  i5=0;
  i=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iwn == 1;
  loop invariant i >= -8;
  loop invariant qdia >= 1;
  loop invariant i5 >= 0;
  loop assigns i, i5, qdia;
*/
while (1) {
      if (!(qdia!=i5)) {
          break;
      }
      i5 = qdia;
      qdia = (qdia+iwn/qdia)/2;
      i = i + qdia;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant iwn >= 1;
  loop invariant i5 >= 1;
  loop invariant iwn <= qdia;
  loop assigns i5, iwn;
*/
while (1) {
      i5 = i5*2;
      iwn++;
      if (iwn>=qdia) {
          break;
      }
  }
}