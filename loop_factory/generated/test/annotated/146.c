int main1(){
  int wat;
  wat=(1%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wat >= 9;
  loop invariant (wat == 9) || (wat >= 90);
  loop assigns wat;
*/
while (wat>0) {
      wat = wat+wat*wat;
  }
}