int main1(){
  int p, a1;
  p=(1%6)+13;
  a1=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == (1%6) + 13;
  loop invariant a1 >= 4;
  loop invariant a1 % 2 == 0;
  loop assigns a1;
*/
while (a1<p&&a1>0) {
      a1 += 1;
      a1 += a1;
  }
}