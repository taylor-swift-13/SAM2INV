int main1(){
  int wp, e, f, vmw, dca;
  wp=138;
  e=0;
  f=0;
  vmw=3;
  dca=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f <= wp;
  loop invariant dca == -4 + 4*f;
  loop invariant e == 0;
  loop invariant wp == 138;
  loop invariant 0 <= f;
  loop assigns dca, f, vmw;
*/
while (f<wp) {
      if (f>=wp/2) {
          vmw += 2;
      }
      dca = dca + e;
      f = f + 1;
      dca += 4;
  }
}