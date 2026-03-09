int main1(){
  int c, mp, y, eymz;
  c=1+11;
  mp=0;
  y=0;
  eymz=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= y;
  loop invariant y <= c;
  loop invariant mp == (y % 6);
  loop invariant eymz == -6 + (y*(y+1))/2;
  loop assigns mp, y, eymz;
*/
while (y<c) {
      mp = (mp+1)%6;
      y++;
      eymz = eymz + y;
  }
}