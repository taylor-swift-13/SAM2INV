int main1(int y){
  int fc, bdz0, dv;
  fc=(y%6)+16;
  bdz0=0;
  dv=y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dv == y + 3 * bdz0;
  loop invariant 0 <= bdz0;
  loop invariant bdz0 <= fc;
  loop invariant fc == (y % 6) + 16;
  loop assigns dv, bdz0;
*/
for (; bdz0+1<=fc; bdz0 += 1) {
      dv = dv + 3;
  }
}