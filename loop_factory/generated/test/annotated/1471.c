int main1(){
  int md, e0, jxy;
  md=40;
  e0=0;
  jxy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e0 == ((2*jxy - 1) % 5) + 1;
  loop invariant 0 <= jxy <= md;
  loop invariant (jxy == 0) <==> (e0 == 0);
  loop assigns jxy, e0;
*/
while (jxy<=md-1) {
      jxy += 1;
      e0 = (e0+1)%5;
      e0 += 1;
  }
}