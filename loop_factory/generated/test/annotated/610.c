int main1(){
  int ba, x, vl, e;
  ba=1*3;
  x=0;
  vl=6;
  e=ba;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 0;
  loop invariant ba <= x + 5;
  loop invariant vl >= 6;
  loop invariant e == 3;
  loop invariant ba >= 0;
  loop assigns vl, ba;
*/
while (x+5<=ba) {
      if (x<ba/2) {
          vl = vl + e;
      }
      else {
          vl++;
      }
      ba = (x+5)-1;
  }
}