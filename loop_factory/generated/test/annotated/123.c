int main1(){
  int g, vxjm, f;
  g=1-2;
  vxjm=g;
  f=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vxjm <= g;
  loop invariant g == -1;
  loop invariant f == 1 || f % 4 == 0;
  loop invariant f > 0;
  loop assigns f, vxjm;
*/
while (vxjm<g) {
      if (f>=6) {
          f = -1;
      }
      if (f<=0) {
          f = 1;
      }
      f += f;
      vxjm = vxjm + 1;
      f += f;
  }
}