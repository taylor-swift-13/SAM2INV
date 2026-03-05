int main1(){
  int r1;
  r1=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r1 == -3 || r1 == 0;
  loop assigns r1;
*/
while (r1!=r1) {
      if (r1>r1) {
          r1 = r1 - r1;
          r1 = r1 + r1;
      }
      else {
          r1 = r1 - r1;
          r1 = r1 + r1;
      }
      r1 = r1%9;
  }
}