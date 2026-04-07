int main1(){
  int s0, vw, n1u, z4, soq, xul;
  s0=(1%32)+20;
  vw=0;
  n1u=s0;
  z4=3;
  soq=s0;
  xul=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= vw;
  loop invariant vw <= s0;
  loop invariant xul == 3 * vw;
  loop invariant n1u >= s0;
  loop invariant z4 >= 3;
  loop invariant soq == s0;
  loop assigns vw, z4, n1u, xul;
*/
while (1) {
      if (!(vw < s0)) {
          break;
      }
      vw = vw + 1;
      z4 = z4*4+(z4%5)+1;
      n1u = n1u*2+(soq%2)+1;
      xul = xul + 3;
  }
}