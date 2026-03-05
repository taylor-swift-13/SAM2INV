int main1(){
  int og4, qt0w, o;
  og4=1;
  qt0w=og4+6;
  o=qt0w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant og4 == 1;
  loop invariant qt0w == og4 + 6;
  loop invariant o >= 7;
  loop assigns o;
*/
while (qt0w>og4) {
      o = o + 1;
      o = o+o*o*o;
  }
}