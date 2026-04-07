int main1(int i){
  int dl, v7, ej;
  dl=80;
  v7=0;
  ej=i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ej == \at(i, Pre) + 3*v7;
  loop invariant v7 <= dl;
  loop invariant ej == i + 3*v7;
  loop invariant 0 <= v7;
  loop assigns ej, v7;
*/
while (v7 < dl) {
      ej += 2;
      v7 += 1;
      ej = ej + 1;
  }
}