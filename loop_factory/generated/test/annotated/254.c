int main1(){
  int j9u, r5, qt;
  j9u=1+4;
  r5=0;
  qt=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qt == 8 + 5*r5;
  loop invariant 0 <= r5;
  loop invariant r5 <= j9u;
  loop invariant j9u == 1 + 4;
  loop assigns r5, qt;
*/
for (; r5<j9u; r5 += 1) {
      qt = qt + 5;
  }
}