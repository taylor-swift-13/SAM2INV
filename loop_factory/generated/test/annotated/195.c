int main1(int z){
  int h;
  h=-14720;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z <= \at(z, Pre);
  loop invariant h <= -14720;
  loop assigns h, z;
*/
while (h+5<0) {
      h = h+h-2;
      h += 1;
      z += h;
  }
}