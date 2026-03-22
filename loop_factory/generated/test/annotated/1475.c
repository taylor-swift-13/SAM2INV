int main1(){
  int z2a, uwdw, bx, mo7w;
  z2a=1;
  uwdw=0;
  bx=0;
  mo7w=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z2a == 1;
  loop invariant 0 <= bx;
  loop invariant bx <= z2a;
  loop invariant 0 <= uwdw;
  loop invariant uwdw < z2a;
  loop invariant mo7w == uwdw;
  loop assigns bx, uwdw, mo7w;
*/
while (bx < z2a) {
      bx += 1;
      uwdw = (uwdw + 1) % z2a;
      mo7w = uwdw;
  }
}