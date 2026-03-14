int main1(){
  int nc, fjv, c, z, la, yq9, h;
  nc=1;
  fjv=0;
  c=0;
  z=(1%28)+10;
  la=nc;
  yq9=fjv;
  h=fjv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z + c*(c-1)/2 == 11;
  loop invariant yq9 == c;
  loop invariant h == yq9;
  loop invariant la == 1;
  loop invariant fjv == 0;
  loop invariant nc == 1;
  loop assigns z, la, yq9, c, h;
*/
while (1) {
      if (!(z>c)) {
          break;
      }
      z = z - c;
      la += fjv;
      yq9 = yq9 + 1;
      c = c + 1;
      h = (la)+(h);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (fjv - nc) == -1;
  loop invariant nc >= 1;
  loop assigns fjv, nc, la, z;
*/
while (1) {
      if (!(z>=1)) {
          break;
      }
      fjv = fjv+1*1;
      nc = nc+1*1;
      la = la+1*1;
      z = z - 1;
      la = la + c;
  }
}