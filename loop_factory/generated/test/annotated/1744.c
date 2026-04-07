int main1(int y){
  int rx, h1j, ao, gd, ves;
  rx=y-2;
  h1j=y;
  ao=6;
  gd=4;
  ves=rx;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rx == \at(y, Pre) - 2;
  loop invariant gd == 4 + 6*(ves - rx);
  loop invariant h1j == y + (ves - rx)*(ves - rx)*(ves - rx) - (ves - rx)*(ves - rx) + 6*(ves - rx);
  loop invariant h1j == \at(y, Pre) + (ves - rx) * (ves - rx) * (ves - rx - 1) + 6 * (ves - rx);
  loop invariant ves >= rx;
  loop invariant ves <= rx + 1;
  loop invariant ao == 3*(ves - rx)*(ves - rx) + (ves - rx) + 6;
  loop invariant (gd - 6*ves) == (16 - 6*y);
  loop assigns h1j, ao, ves, gd;
*/
while (1) {
      if (ves>rx) {
          break;
      }
      h1j += ao;
      ao = ao + gd;
      ves = (1)+(ves);
      gd += 6;
  }
}