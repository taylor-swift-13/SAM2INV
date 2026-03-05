int main1(){
  int kp, kr, g0w;
  kp=1;
  kr=kp;
  g0w=kr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kr == 1;
  loop invariant g0w >= kr;
  loop invariant kp == 1;
  loop invariant (g0w % 7 == 1);
  loop assigns g0w;
*/
while (kr>=1) {
      g0w = g0w + 3;
      g0w += g0w;
  }
}