int main1(){
  int z2b, zvd, at, xy0, x2, qk;
  z2b=(1%34)+5;
  zvd=0;
  at=5;
  xy0=zvd;
  x2=1;
  qk=zvd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 5 <= at <= z2b + 1;
  loop invariant xy0 == 0;
  loop invariant (at == 5) ==> (x2 == 1);
  loop invariant z2b == 6;
  loop invariant (x2 == 1) || (x2 == 5);
  loop invariant qk >= 0;
  loop assigns at, x2, qk, xy0;
*/
while (1) {
      if (!(at<=z2b)) {
          break;
      }
      xy0 = xy0*at;
      if (at<z2b) {
          x2 = x2*at;
      }
      qk = qk+(x2%8);
      at = at + 1;
  }
}