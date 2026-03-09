int main1(){
  int l7, mh5;
  l7=54;
  mh5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= mh5;
  loop invariant mh5 <= l7;
  loop invariant l7 == 54;
  loop assigns mh5;
*/
while (1) {
      if (!(mh5<=l7-1)) {
          break;
      }
      mh5 += 1;
  }
}