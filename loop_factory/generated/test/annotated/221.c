int main1(){
  int p, p36;
  p=15;
  p36=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 15;
  loop invariant p36 <= p + 2;
  loop invariant p36 % 3 == 2;
  loop assigns p36;
*/
while (p36<p) {
      p36 = p36 + 3;
  }
}