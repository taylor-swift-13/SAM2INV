int main1(){
  int d8ey, vm, gt, h;
  d8ey=(1%14)+14;
  vm=d8ey;
  gt=d8ey;
  h=d8ey;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == d8ey;
  loop invariant gt == d8ey + 2*h*(d8ey - vm);
  loop invariant (d8ey - vm) >= 0;
  loop invariant 0 <= vm;
  loop assigns gt, vm;
*/
while (vm>=1) {
      gt = gt+h+h;
      vm = vm - 1;
  }
}