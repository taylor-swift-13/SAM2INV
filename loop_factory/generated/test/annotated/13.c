int main1(){
  int jsx;
  jsx=-14593;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jsx <= -14593;
  loop assigns jsx;
*/
while (jsx+1<0) {
      jsx = jsx+jsx+2;
      jsx += 2;
  }
}