int main1(){
  int bj8g, s9, ze, qan;
  bj8g=62;
  s9=0;
  ze=s9;
  qan=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bj8g == 62;
  loop invariant qan == -3;
  loop invariant (s9 == 0) || (s9 == bj8g);
  loop invariant 0 <= s9;
  loop invariant s9 <= bj8g;
  loop invariant (s9 == bj8g) ==> (ze == qan);
  loop invariant (s9 != bj8g) ==> (ze == 0);
  loop assigns ze, s9;
*/
while (s9<=bj8g-1) {
      if (s9<bj8g/2) {
          ze += qan;
      }
      else {
          ze++;
      }
      s9 = bj8g;
  }
}