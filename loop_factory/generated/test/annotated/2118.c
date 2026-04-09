int main1(){
  int za5q, su, lt, s, x;
  za5q=95;
  su=0;
  lt=1;
  s=0;
  x=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == su * su;
  loop invariant x == 1 + 2 * su;
  loop invariant 0 <= su;
  loop invariant su <= za5q;
  loop invariant lt >= 1;
  loop invariant 0 <= s % 5;
  loop invariant s % 5 <= 4;
  loop assigns su, s, x, lt;
*/
while (su < za5q) {
      s += x;
      lt = lt*4+(s%5)+0;
      x += 2;
      su++;
  }
}