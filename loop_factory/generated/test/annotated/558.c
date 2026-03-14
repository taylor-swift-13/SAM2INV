int main1(){
  int uy, vdg, z7a;
  uy=38;
  vdg=0;
  z7a=uy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vdg - 2*z7a == -76;
  loop invariant z7a >= uy;
  loop invariant z7a >= 0;
  loop assigns vdg, z7a;
*/
while (1) {
      if (!(vdg<uy&&z7a>0)) {
          break;
      }
      vdg = (1)+(vdg);
      z7a -= 1;
      vdg = vdg + 3;
      z7a = z7a + 3;
  }
}