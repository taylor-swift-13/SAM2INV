int main1(){
  int c, ey9, l, rub;
  c=1;
  ey9=0;
  l=0;
  rub=1*3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ey9 == 0) ==> (l == 0 && rub == 3);
  loop invariant 0 <= ey9 <= c;
  loop invariant l >= 0;
  loop invariant l <= rub;
  loop assigns ey9, l, rub;
*/
while (1) {
      if (!(ey9 < c)) {
          break;
      }
      ey9 = ey9 + 1;
      l = l + rub;
      rub += l;
  }
}