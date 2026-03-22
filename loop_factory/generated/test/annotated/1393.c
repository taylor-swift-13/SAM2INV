int main1(){
  int qwz7, lvkd, qr8, x, qq, f;
  qwz7=1;
  lvkd=0;
  qr8=1;
  x=6;
  qq=0;
  f=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 6 + 2*qq;
  loop invariant lvkd == (qq*(qq*qq + 6*qq - 4))/3;
  loop invariant 0 <= qq <= qwz7 + 1;
  loop invariant f == qq*(qq + 7);
  loop invariant qr8 == 1 + 5*qq + qq*qq;
  loop assigns lvkd, qq, qr8, x, f;
*/
while (1) {
      if (!(qq<=qwz7)) {
          break;
      }
      lvkd = lvkd + qr8;
      qq++;
      qr8 += x;
      x += 2;
      f += x;
  }
}