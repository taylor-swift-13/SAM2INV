int main1(){
  int uau1, me, hu, l, ol, ig;
  uau1=(1%19)+8;
  me=0;
  hu=0;
  l=me;
  ol=uau1;
  ig=uau1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ol == uau1 + 4*(ig - uau1);
  loop invariant l  == 2*(ig - uau1)*(ig - uau1) + 7*(ig - uau1);
  loop invariant 0 <= ig - uau1 <= 1;
  loop invariant 0 <= hu;
  loop invariant 0 <= l;
  loop invariant 0 <= ol;
  loop invariant hu % 2 == 0;
  loop invariant ol == 4*ig - 27;
  loop assigns hu, l, ol, ig;
*/
while (1) {
      if (ig>uau1) {
          break;
      }
      hu += l;
      l = l + ol;
      hu = hu*2;
      ol = (4)+(ol);
      ig++;
  }
}