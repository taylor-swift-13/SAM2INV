int main1(){
  int rk, uz, b, baj;
  rk=69;
  uz=0;
  b=rk;
  baj=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= uz;
  loop invariant uz <= rk;
  loop invariant b == (rk + ((uz*(uz+1))/2));
  loop invariant baj == b - uz;
  loop assigns uz, b, baj;
*/
while (uz < rk) {
      uz += 1;
      if (b != baj) {
          baj = b;
      }
      b = b + uz;
  }
}