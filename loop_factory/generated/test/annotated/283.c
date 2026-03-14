int main1(int a){
  int av, z, cr4;
  av=73;
  z=0;
  cr4=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (cr4 - a) == 2*z;
  loop invariant z <= av;
  loop invariant a <= \at(a, Pre);
  loop invariant cr4 + a == 2 * \at(a, Pre);
  loop assigns cr4, a, z;
*/
while (1) {
      cr4++;
      a -= 1;
      z += 1;
      if (z>=av) {
          break;
      }
  }
}