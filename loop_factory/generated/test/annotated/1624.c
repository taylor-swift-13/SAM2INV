int main1(){
  int rr0, d, po;
  rr0=50;
  d=0;
  po=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (d <= rr0);
  loop invariant ((po == 0) ==> (d == 0)) && ((po > 0) ==> (d == rr0));
  loop invariant (0 <= po && po <= 1);
  loop invariant po <= rr0;
  loop invariant (d == 0) ==> (po == 0);
  loop assigns po, d;
*/
while (1) {
      if (!(d < rr0)) {
          break;
      }
      po++;
      d = rr0;
  }
}