int main1(){
  int ne, l5qd, y, e1, b7;
  ne=1;
  l5qd=0;
  y=0;
  e1=0;
  b7=ne;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e1 == y*(y+1)/2;
  loop invariant 0 <= l5qd;
  loop invariant l5qd <= ne;
  loop invariant ne == 1;
  loop invariant 0 <= y;
  loop assigns y, e1, l5qd;
*/
while (l5qd<=ne-1) {
      y++;
      e1 = e1 + y;
      l5qd = ne;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ne == 1;
  loop invariant b7 >= 1;
  loop invariant b7 <= ne;
  loop assigns y, b7;
*/
while (1) {
      if (!(b7<ne)) {
          break;
      }
      y = ne-b7;
      b7 = b7 + 1;
      y = y + y;
  }
}