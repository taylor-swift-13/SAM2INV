int main1(){
  int dr, s;
  dr=69;
  s=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dr == 69;
  loop invariant s <= 2*dr - 1;
  loop invariant (s == 0) || (s % 2 == 1);
  loop assigns s;
*/
while (s<dr) {
      s = s + s;
      s++;
  }
}