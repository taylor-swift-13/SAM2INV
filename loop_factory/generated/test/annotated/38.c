int main1(){
  int t, mb2q, aa;
  t=1-3;
  mb2q=0;
  aa=t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aa == 0 || aa == t;
  loop invariant mb2q == 0;
  loop invariant t == 1 - 3;
  loop assigns aa;
*/
while (mb2q<=t-1) {
      aa += aa;
      aa -= aa;
  }
}