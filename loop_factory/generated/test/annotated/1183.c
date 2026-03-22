int main1(){
  int z, y, mjr, yu, e280, tp;
  z=1+7;
  y=z+2;
  mjr=(1%20)+1;
  yu=(1%25)+1;
  e280=0;
  tp=z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (y == z + 2) &&
                    ((0 <= yu) && (yu <= 2)) &&
                    (tp >= z) &&
                    (((tp - z) % y) == 0) &&
                    ((0 <= tp - z) && ((tp - z) <= 2*y));
  loop invariant (mjr % 2 == 0);
  loop invariant (mjr >= 2);
  loop invariant (e280 >= 0);
  loop invariant (tp >= z);
  loop invariant (yu >= 0);
  loop invariant e280 % 2 == 0;
  loop invariant y == 10;
  loop invariant z == 8;
  loop invariant tp + y*yu == z + 2*y;
  loop assigns e280, yu, tp, mjr;
*/
while (yu!=0) {
      if (yu%2==1) {
          e280 = e280 + mjr;
          yu -= 1;
      }
      else {
      }
      tp = tp + y;
      yu = yu/2;
      mjr = 2*mjr;
      if (tp+1<z) {
          tp = tp%7;
      }
  }
}