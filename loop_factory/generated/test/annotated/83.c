int main1(){
  int ux, i3v;
  ux=0;
  i3v=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i3v >= 0;
  loop invariant ux >= 0;
  loop invariant ux + i3v <= 9;
  loop assigns ux, i3v;
*/
while (i3v>0&&i3v>0) {
      if (ux%2==0) {
          i3v -= 1;
      }
      else {
          i3v -= 1;
      }
      ux = ux + 1;
      i3v -= i3v;
  }
}