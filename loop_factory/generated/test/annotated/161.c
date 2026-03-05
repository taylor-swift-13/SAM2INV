int main1(){
  int c;
  c=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == 0 || c == 1;
  loop assigns c;
*/
while (c!=c) {
      if (c>c) {
          c = c - c;
          c = c - c;
          c = c - c;
      }
      else {
          c = c - c;
          c = c - c;
          c = c - c;
      }
      c = c*c;
  }
}