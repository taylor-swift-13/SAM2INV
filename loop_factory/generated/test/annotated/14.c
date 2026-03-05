int main1(){
  int oo;
  oo=-104;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oo % 4 == 0;
  loop invariant oo <= -104;
  loop assigns oo;
*/
while (oo<=-3) {
      oo = oo+oo+1;
      oo = oo + 3;
  }
}