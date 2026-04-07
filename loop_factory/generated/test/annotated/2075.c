int main1(){
  int ji, b3, o8, w73;
  ji=1;
  b3=ji + 10;
  o8=ji + 20;
  w73=ji + 30;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ji == 1;
  loop invariant ji <= b3;
  loop invariant b3 <= ji + 10;
  loop invariant o8 == (2 * b3) - ji;
  loop invariant w73 == (3 * b3) - (2 * ji);
  loop assigns b3, o8, w73;
*/
while (b3 > ji) {
      o8 -= 2;
      b3 = b3 - 1;
      w73 = w73 - 3;
  }
}