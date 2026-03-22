int main1(){
  int fn, g9;
  fn=115;
  g9=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fn == 115;
  loop invariant (1 <= g9);
  loop invariant (g9 <= fn);
  loop assigns g9;
*/
for (; g9+1<=fn; g9++) {
  }
}