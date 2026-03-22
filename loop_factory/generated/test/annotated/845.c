int main1(){
  int b, na, y, h7, vf;
  b=80;
  na=0;
  y=na;
  h7=-1;
  vf=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 80;
  loop invariant y == 0;
  loop invariant (h7 == -1 || h7 == 0);
  loop invariant vf >= 0;
  loop invariant (na == 0) || (na == b);
  loop invariant 0 <= na <= b;
  loop invariant (na == 0) ==> (vf == 80);
  loop assigns y, h7, vf, na;
*/
while (1) {
      if (!(na<=b-1)) {
          break;
      }
      y = y*2;
      h7 = h7/2;
      vf = vf*4+(y%5)+3;
      na = b;
  }
}