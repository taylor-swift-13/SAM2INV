int main1(){
  int vvk;
  vvk=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vvk == 12;
  loop assigns vvk;
*/
while (vvk>0) {
      vvk++;
      vvk -= 1;
  }
}