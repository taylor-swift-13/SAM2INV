int main1(int f,int r){
  int fr, x, a;
  fr=(r%36)+17;
  x=fr;
  a=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == 4 + 3*(x - fr);
  loop invariant x <= fr;
  loop invariant f == \at(f, Pre);
  loop invariant r == \at(r, Pre);
  loop invariant fr == (r % 36) + 17;
  loop invariant a >= 4;
  loop assigns a, x;
*/
while (x<fr) {
      a = a + 3;
      x = x + 1;
  }
}