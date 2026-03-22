int main1(int y,int v){
  int no0, jc;
  no0=165;
  jc=no0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == \at(y, Pre) + (165 - jc) * v;
  loop invariant y == \at(y,Pre) + (no0 - jc) * \at(v,Pre);
  loop invariant 0 <= jc <= no0;
  loop invariant y == \at(y, Pre) + (no0 - jc) * v;
  loop invariant y == \at(y,Pre) + (165 - jc) * \at(v,Pre);
  loop assigns y, jc;
*/
for (; jc>=1; jc -= 1) {
      y += v;
  }
}