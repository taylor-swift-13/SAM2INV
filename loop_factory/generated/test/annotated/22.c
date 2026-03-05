int main1(int c,int n){
  int s5;
  s5=11;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s5 == 11;
  loop invariant c == \at(c, Pre);
  loop invariant n == \at(n, Pre);
  loop assigns s5;
*/
while (s5>0) {
      s5 = s5 + 1;
      s5--;
  }
}