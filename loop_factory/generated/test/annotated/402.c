int main1(){
  int dr, wcm, bb, h9yg, c;
  dr=(1%31)+4;
  wcm=dr;
  bb=15;
  h9yg=1;
  c=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wcm - c == dr;
  loop invariant 0 <= bb;
  loop invariant c <= dr;
  loop invariant c == h9yg - 1;
  loop assigns bb, c, wcm, h9yg;
*/
while (bb>0&&h9yg<=dr) {
      if (bb>h9yg) {
          bb = bb - h9yg;
      }
      else {
          bb = 0;
      }
      c = c + 1;
      wcm = wcm + 1;
      h9yg++;
  }
}