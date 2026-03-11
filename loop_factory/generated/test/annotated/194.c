int main1(){
  int l5eu, p8, dc2s, b9ya, fe;
  l5eu=48;
  p8=0;
  dc2s=1;
  b9ya=0;
  fe=p8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b9ya == (dc2s - 1) * (dc2s - 1);
  loop invariant 1 <= dc2s <= l5eu + 1;
  loop invariant 2 * (fe + 1) == dc2s * (dc2s + 1);
  loop assigns b9ya, dc2s, fe;
*/
while (dc2s<=l5eu) {
      b9ya = b9ya+2*dc2s-1;
      dc2s++;
      fe += dc2s;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fe >= p8;
  loop invariant 2 * dc2s - 2 * b9ya - 2 * fe == -3 * l5eu * l5eu - l5eu + 2;
  loop invariant 2 * dc2s - fe * (fe + 1) == -1499302;
  loop invariant b9ya == (dc2s-1)*(dc2s-1);
  loop invariant fe == ((dc2s*(dc2s+1))/2) - 1;
  loop invariant 1 <= dc2s;
  loop assigns b9ya, fe, dc2s;
*/
while (1) {
      if (!(fe<p8)) {
          break;
      }
      b9ya = b9ya + fe;
      fe += 1;
      dc2s = dc2s + fe;
  }
}