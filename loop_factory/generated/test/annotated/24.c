int main1(){
  int o, b6v;
  o=1*2;
  b6v=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= b6v;
  loop invariant b6v <= o;
  loop invariant o == 2;
  loop assigns b6v;
*/
while (b6v<=o-1) {
      b6v = b6v + 1;
  }
}