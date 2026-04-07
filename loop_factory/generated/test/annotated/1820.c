int main1(){
  int q, g3, d, igt, ldj, hp1;
  q=(1%21)+7;
  g3=0;
  d=g3;
  igt=0;
  ldj=q;
  hp1=(1%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ldj - igt == 8;
  loop invariant d % 4 == 0;
  loop invariant 0 <= hp1;
  loop invariant igt >= 0;
  loop invariant (ldj == q + igt);
  loop assigns d, ldj, igt, hp1;
*/
while (1) {
      if (!(hp1>=1)) {
          break;
      }
      d = d+igt*igt;
      ldj = ldj+hp1*hp1;
      igt = (hp1*hp1)+(igt);
      hp1 -= 1;
      d = d*4;
  }
}