int main1(int h){
  int yuf8, iz, zue, o9f, xf;
  yuf8=18;
  iz=0;
  zue=h;
  o9f=iz;
  xf=iz;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o9f == 0;
  loop invariant yuf8 == 18;
  loop invariant 0 <= iz <= yuf8;
  loop invariant (iz == 0) ==> (zue == h);
  loop invariant (iz == yuf8) ==> (zue == h*3);
  loop invariant (iz == 0) ==> (xf == 0);
  loop invariant ((iz == 0 && zue == h) || (iz == yuf8 && zue == h*3));
  loop assigns zue, o9f, xf, iz;
*/
while (1) {
      if (!(iz<yuf8)) {
          break;
      }
      zue = zue*3;
      o9f = o9f/3;
      xf = xf*2+(o9f%6)+2;
      iz = yuf8;
  }
}