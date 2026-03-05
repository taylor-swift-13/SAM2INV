int main1(){
  int fr, s5g;
  fr=66;
  s5g=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s5g <= fr + 3;
  loop invariant fr == 66;
  loop invariant (s5g - 1) % 3 == 0;
  loop invariant s5g >= 1;
  loop assigns s5g;
*/
while (s5g<=fr) {
      s5g++;
      s5g += 2;
  }
}