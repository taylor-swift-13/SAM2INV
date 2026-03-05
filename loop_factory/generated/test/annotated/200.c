int main1(int l,int r){
  int z40;
  z40=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z40 >= 0;
  loop invariant z40 <= 5;
  loop invariant r == \at(r,Pre);
  loop invariant l == \at(l, Pre) + 2 * \at(r, Pre) * ((5 - z40) / 5);
  loop invariant (l - \at(l, Pre) == 0) || (l - \at(l, Pre) == 2*r);
  loop assigns z40, l;
*/
while (z40!=0&&z40!=0) {
      if (z40>z40) {
          z40 -= z40;
      }
      else {
          z40 -= z40;
      }
      l = l+z40-z40;
      l = l+r+r;
  }
}