int main1(int y,int c){
  int oja, a3, b9;
  oja=(y%8)+11;
  a3=0;
  b9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oja == \at(y, Pre) % 8 + 11
                   && c == \at(c, Pre)
                   && a3 == 0
                   && (b9 == 0 || b9 == oja + 1);
  loop invariant c == \at(c, Pre);
  loop invariant oja == \at(y, Pre) % 8 + 11;
  loop invariant (b9 == 0) || (b9 == oja + 1);
  loop invariant a3 == 0;
  loop invariant y == \at(y, Pre);
  loop assigns b9, y;
*/
while (a3<oja) {
      b9 = oja-b9;
      b9 += 1;
      y += a3;
  }
}