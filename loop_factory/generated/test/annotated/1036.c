int main1(){
  int p5, g, a2, sj, js3;
  p5=1;
  g=0;
  a2=1;
  sj=0;
  js3=13;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 1 <= a2;
  loop invariant a2 <= p5 + 1;
  loop invariant sj == (a2 - 1) * (a2 - 1);
  loop invariant js3 == 13 + (((a2 - 1) * a2 * (2 * a2 - 1)) / 6);
  loop invariant p5 == 1;
  loop invariant js3 == a2 + 12;
  loop invariant js3 >= 13;
  loop invariant js3 == 13 + sj;
  loop assigns sj, js3, a2;
*/
while (a2<=p5) {
      sj = (sj+2*a2)+(-(1));
      js3 = js3 + sj;
      a2 = a2 + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a2 >= 1;
  loop invariant g == 0;
  loop invariant p5 == 1;
  loop invariant a2 <= p5 + 1;
  loop invariant js3 == 13 + ((a2 - 1) * a2 * (2*a2 - 1)) / 6;
  loop assigns a2, js3, p5;
*/
while (1) {
      if (!(js3<g)) {
          break;
      }
      a2 = g-js3;
      js3 += 1;
      p5 += js3;
  }
}