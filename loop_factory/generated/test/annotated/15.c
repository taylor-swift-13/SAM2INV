int main1(){
  int o;
  o=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 5;
  loop assigns o;
*/
while (o>0) {
      o = o + 1;
      o--;
  }
}