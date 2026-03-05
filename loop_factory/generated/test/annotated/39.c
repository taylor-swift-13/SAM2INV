int main1(int n){
  int e, g2g, eq;
  e=36;
  g2g=e;
  eq=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g2g == 36;
  loop invariant e == 36;
  loop invariant eq >= 36;
  loop invariant n == \at(n, Pre);
  loop assigns eq;
*/
while (g2g>0) {
      eq++;
  }
}