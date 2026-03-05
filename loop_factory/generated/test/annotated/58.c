int main1(int w){
  int f5, as72, ij;
  f5=w;
  as72=f5;
  ij=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ij >= -2;
  loop invariant f5 == \at(w, Pre);
  loop invariant as72 == f5;
  loop invariant w == \at(w,Pre) * (ij + 3);
  loop assigns ij, w;
*/
while (as72>=4) {
      ij++;
      w = w + f5;
  }
}