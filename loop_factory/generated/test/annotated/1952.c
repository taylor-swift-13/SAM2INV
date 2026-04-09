int main1(){
  int qb, ast7, yn, u5;
  qb=188;
  ast7=0;
  yn=-2;
  u5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= ast7);
  loop invariant (ast7 <= qb);
  loop invariant u5 == ast7 * ast7;
  loop invariant 6 * (yn + 2) == ast7 * (ast7 + 1) * (2 * ast7 + 1);
  loop assigns ast7, u5, yn;
*/
while (ast7 < qb) {
      u5 = u5 + 2*ast7 + 1;
      ast7 += 1;
      yn += u5;
  }
}