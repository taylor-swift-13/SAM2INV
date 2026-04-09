int main1(){
  int ev, vm2, l, g;
  ev=(1%22)+17;
  vm2=0;
  l=0;
  g=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l - vm2 + (g*(g+1))/2 == 10;
  loop invariant vm2 <= ev;
  loop invariant 0 <= g;
  loop invariant g <= 4;
  loop invariant (g + vm2) == 4;
  loop invariant 2 * l == vm2 * (11 - vm2);
  loop assigns vm2, l, g;
*/
while (vm2<ev&&g>0) {
      vm2++;
      l = l + g;
      l = l + 1;
      g -= 1;
  }
}