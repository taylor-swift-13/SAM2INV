int main1(){
  int x, y, r, kg, atll, a;
  x=1+15;
  y=0;
  r=0;
  kg=0;
  atll=0;
  a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= a;
  loop invariant 0 <= atll;
  loop invariant 0 <= kg;
  loop invariant x == 16;
  loop invariant 0 <= a + atll + kg;
  loop invariant a + atll + kg <= y;
  loop invariant 0 <= y <= x;
  loop invariant 0 <= r - y <= (x - 1) / 9 + 1;
  loop invariant r - y == ((y - 1) / 9) - ((y - 1) / 18) - ((y - 1) / 63) + ((y - 1) / 126);
  loop assigns a, atll, kg, r, y;
*/
while (1) {
      if (!(y<x)) {
          break;
      }
      if (!(!(y%9==0))) {
          if (y%6==0) {
              atll = atll + 1;
          }
          else {
              if (y%7==0) {
                  kg = kg + 1;
              }
              else {
                  r = r + 1;
              }
          }
      }
      else {
          a++;
      }
      r = r + 1;
      y++;
  }
}