int main1(){
  int cqv, ai, d2j, uex, z1, q;
  cqv=70;
  ai=0;
  d2j=ai;
  uex=0;
  z1=cqv;
  q=ai;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cqv == 70;
  loop invariant q == 0;
  loop invariant z1 == 70;
  loop invariant uex == 0;
  loop invariant d2j == z1 * ai;
  loop invariant 0 <= ai <= cqv;
  loop assigns ai, d2j, uex, z1;
*/
while (ai < cqv) {
      d2j = d2j + z1;
      uex = uex + q;
      ai++;
      z1 += uex;
  }
}