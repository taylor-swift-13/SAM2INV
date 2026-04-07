int main1(){
  int pydj, e, uz4, kej;
  pydj=1*2;
  e=0;
  uz4=25;
  kej=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pydj == 2;
  loop invariant kej == 2*uz4 - 47;
  loop invariant e >= 0;
  loop invariant e * e <= pydj;
  loop invariant e <= pydj;
  loop invariant (uz4 >= 25);
  loop assigns e, uz4, kej;
*/
while (1) {
      if (!((e+1)*(e+1) <= pydj)) {
          break;
      }
      e += 1;
      uz4 = uz4 + uz4;
      kej = kej + uz4;
  }
}