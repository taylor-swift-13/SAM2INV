int main1(){
  int w7, nyit, ic;
  w7=1+10;
  nyit=1;
  ic=w7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nyit == 1;
  loop invariant w7 == 11;
  loop invariant ic >= 11;
  loop invariant (ic % 2 == 1);
  loop invariant (nyit < w7/2) ==> ((ic + 1) % 12 == 0);
  loop assigns ic;
*/
while (nyit+2<=w7) {
      if (nyit<w7/2) {
          ic += ic;
      }
      else {
          ic = ic + 1;
      }
      ic += nyit;
  }
}