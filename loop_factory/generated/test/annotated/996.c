int main1(int z,int i){
  int r, e;
  r=(z%6)+17;
  e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (0 <= e);
  loop invariant (e <= r);
  loop invariant r == ((z % 6) + 17);
  loop assigns e;
*/
while (1) {
      if (!(e<r)) {
          break;
      }
      e += 1;
  }
}