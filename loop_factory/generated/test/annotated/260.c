int main1(){
  int j7, ay;
  j7=1;
  ay=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ay >= 0;
  loop invariant ay % 4 == 0;
  loop invariant ay <= j7;
  loop invariant j7 == 1;
  loop assigns ay;
*/
while (1) {
      if (!(ay<=j7-4)) {
          break;
      }
      ay += 4;
  }
}