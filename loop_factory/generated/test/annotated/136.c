int main1(){
  int ti, got, tw6u, a;
  ti=139;
  got=ti;
  tw6u=-6;
  a=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ti == 139;
  loop invariant a == -4;
  loop invariant got >= 139;
  loop invariant tw6u == (-6 + (got - 139));
  loop assigns got, tw6u;
*/
while (1) {
      if (!(got-4>=0)) {
          break;
      }
      if (got<ti/2) {
          tw6u = tw6u + a;
      }
      else {
          tw6u++;
      }
      got = got + 1;
  }
}