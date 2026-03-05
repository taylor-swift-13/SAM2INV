int main1(){
  int y;
  y=(1%8)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (y >= 2) || (y <= -2);
  loop assigns y;
*/
while (y!=0) {
      if (y+1==y) {
          y++;
          y = 0;
      }
      else {
          y++;
      }
      y -= 1;
      y = y*2;
  }
}