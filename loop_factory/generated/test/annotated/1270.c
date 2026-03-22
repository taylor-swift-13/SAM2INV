int main1(){
  int l3ew, j, zi, u, kr;
  l3ew=1;
  j=l3ew;
  zi=0;
  u=-5;
  kr=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l3ew == 1;
  loop invariant zi == 0;
  loop invariant (kr - 1) % 3 == 0;
  loop invariant u <= 0;
  loop invariant kr >= 1;
  loop invariant ((j == 1 && kr == 1 && u == -5 && zi == 0 && l3ew == 1) ||
                    (j == 2 && kr == 4 && u == -1 && zi == 0 && l3ew == 1));
  loop invariant (((j == 1) ==> (kr == 1)) && ((j == 2) ==> (kr == 4)));
  loop invariant (j <= 2);
  loop assigns u, kr, zi, j;
*/
while (1) {
      if (!(j>=3)) {
          break;
      }
      u = u/4;
      kr = kr + 3;
      zi = zi*4;
      j = 2;
  }
}