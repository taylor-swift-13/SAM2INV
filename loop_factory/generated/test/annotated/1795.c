int main1(){
  int c2gr, jv, n, w5, z4;
  c2gr=(1%22)+15;
  jv=0;
  n=-4;
  w5=0;
  z4=(1%6)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z4 >= 3;
  loop invariant n <= -4;
  loop invariant jv >= 0;
  loop invariant 0 <= w5 <= c2gr;
  loop assigns n, w5, jv, z4;
*/
while (1) {
      if (!(w5<c2gr)) {
          break;
      }
      n = n*z4;
      w5++;
      jv = jv*z4+4;
      z4 = z4*2+(jv%4)+1;
  }
}